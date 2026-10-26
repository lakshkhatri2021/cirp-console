/* In-browser engine for the standalone console.
 *
 * When the console is opened from a link instead of from console/server.py,
 * there is no Python process to talk to. This file is a line-for-line port of
 * the backend so the same interface still works:
 *   - IncidentService     port of src/incident_module.py
 *   - telemetry           port of console/telemetry.py
 *   - AnomalyScorer       scores with the exported Isolation Forest (model.json)
 *   - Platform            port of the Platform class in console/server.py
 *   - LocalBackend        answers the same /api/... requests as the server
 *
 * tests/parity_check.js runs the same scenario through this port and through
 * the Python module and checks that the results are identical.
 */
(function (root) {
  "use strict";

  // ------------------------------------------------------------ SHA-256
  function sha256(ascii) {
    const K = [], H = [];
    let n = 2, c = 0;
    const isPrime = (x) => { for (let f = 2; f * f <= x; f++) if (x % f === 0) return false; return true; };
    while (c < 64) {
      if (isPrime(n)) {
        if (c < 8) H[c] = (Math.pow(n, 1 / 2) * 4294967296) | 0;
        K[c++] = (Math.pow(n, 1 / 3) * 4294967296) | 0;
      }
      n++;
    }
    const bytes = new TextEncoder().encode(ascii);
    const l = bytes.length, words = [];
    for (let i = 0; i < l; i++) words[i >> 2] |= bytes[i] << ((3 - i) % 4) * 8;
    words[l >> 2] |= 0x80 << ((3 - l) % 4) * 8;
    const total = (((l + 8) >> 6) + 1) * 16;
    while (words.length < total) words.push(0);
    for (let i = 0; i < total; i++) words[i] |= 0;
    words[total - 1] = l * 8;
    const h = H.slice();
    const rotr = (x, r) => (x >>> r) | (x << (32 - r));
    for (let j = 0; j < total; j += 16) {
      const w = words.slice(j, j + 16);
      let [a, b, cc, d, e, f, g, hh] = h;
      for (let i = 0; i < 64; i++) {
        if (i >= 16) {
          const w15 = w[i - 15], w2 = w[i - 2];
          w[i] = (w[i - 16] + (rotr(w15, 7) ^ rotr(w15, 18) ^ (w15 >>> 3)) + w[i - 7] +
                  (rotr(w2, 17) ^ rotr(w2, 19) ^ (w2 >>> 10))) | 0;
        }
        const t1 = (hh + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) | 0;
        const t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & cc) ^ (b & cc))) | 0;
        hh = g; g = f; f = e; e = (d + t1) | 0; d = cc; cc = b; b = a; a = (t1 + t2) | 0;
      }
      h[0] = (h[0] + a) | 0; h[1] = (h[1] + b) | 0; h[2] = (h[2] + cc) | 0; h[3] = (h[3] + d) | 0;
      h[4] = (h[4] + e) | 0; h[5] = (h[5] + f) | 0; h[6] = (h[6] + g) | 0; h[7] = (h[7] + hh) | 0;
    }
    return h.map((x) => (x >>> 0).toString(16).padStart(8, "0")).join("");
  }

  // ------------------------------------------------------------ time helpers
  const pad = (x, w = 2) => String(x).padStart(w, "0");
  // Python datetime.isoformat() for a naive local datetime
  function isoformat(d) {
    const base = `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}T` +
                 `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
    return d.getMilliseconds() ? `${base}.${pad(d.getMilliseconds(), 3)}000` : base;
  }
  const isoSeconds = (d) => isoformat(new Date(Math.floor(d.getTime() / 1000) * 1000));
  const hms = (d) => `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
  const addMinutes = (d, m) => new Date(d.getTime() + m * 60000);
  const fmtG = (x) => String(Number(Number(x).toPrecision(6)));

  // ------------------------------------------------- port of incident_module
  const Severity = { CRITICAL: "Critical", HIGH: "High", MEDIUM: "Medium", LOW: "Low" };
  const Status = { NEW: "New", ASSIGNED: "Assigned", ACKNOWLEDGED: "Acknowledged",
    IN_PROGRESS: "In Progress", ESCALATED: "Escalated", RESOLVED: "Resolved",
    REOPENED: "Reopened", CLOSED: "Closed" };
  const DEDUP_WINDOW_MINUTES = 15;
  const SLA_POLICY = { Critical: [5, 120], High: [15, 240], Medium: [30, 480], Low: [60, 1440] };
  const S = Status;
  const TRANSITIONS = {
    [S.NEW]: [S.ASSIGNED],
    [S.ASSIGNED]: [S.ACKNOWLEDGED, S.ESCALATED],
    [S.ACKNOWLEDGED]: [S.IN_PROGRESS, S.ESCALATED],
    [S.ESCALATED]: [S.IN_PROGRESS],
    [S.IN_PROGRESS]: [S.RESOLVED, S.ESCALATED],
    [S.RESOLVED]: [S.REOPENED, S.CLOSED],
    [S.REOPENED]: [S.IN_PROGRESS],
    [S.CLOSED]: [],
  };
  const OPEN = new Set([S.NEW, S.ASSIGNED, S.ACKNOWLEDGED, S.IN_PROGRESS, S.ESCALATED, S.REOPENED]);

  class ValidationError extends Error {}
  class InvalidTransitionError extends Error {}

  class IncidentService {
    constructor(engineers) {
      this.engineers = engineers || [];
      this.incidents = [];
      this.counter = 0;
    }
    static validateEvent(e) {
      if (!e.resource_id || !e.resource_id.trim()) throw new ValidationError("resource_id must not be empty");
      if (!e.anomaly_type || !e.anomaly_type.trim()) throw new ValidationError("anomaly_type must not be empty");
      if (e.observed_value < 0) throw new ValidationError("observed_value must not be negative");
    }
    findOpenDuplicate(e) {
      const win = DEDUP_WINDOW_MINUTES * 60000;
      return this.incidents.find((i) => OPEN.has(i.status) && i.resource_id === e.resource_id &&
        i.anomaly_type === e.anomaly_type && e.detected_at - i.created_at <= win) || null;
    }
    createIncident(e, actor = "detection-engine") {
      IncidentService.validateEvent(e);
      const dup = this.findOpenDuplicate(e);
      if (dup) {
        dup.linked_events.push(e);
        this.audit(dup, e.detected_at, actor, "EVENT_LINKED", dup.status, dup.status);
        return dup;
      }
      this.counter += 1;
      const [resp, res] = IncidentService.computeDeadlines(e.severity, e.detected_at);
      const inc = { incident_id: `INC-${pad(this.counter, 4)}`, resource_id: e.resource_id,
        anomaly_type: e.anomaly_type, severity: e.severity, created_at: e.detected_at,
        response_due_at: resp, resolution_due_at: res, status: S.NEW, assignee: null,
        resolved_at: null, is_breached: false, linked_events: [e], audit: [] };
      this.incidents.push(inc);
      this.audit(inc, e.detected_at, actor, "CREATED", null, S.NEW);
      const owner = this.resolveOwner();
      if (owner) {
        inc.assignee = owner;
        owner.open_incidents += 1;
        this.changeStatus(inc, S.ASSIGNED, e.detected_at, "routing-policy");
      }
      return inc;
    }
    static computeDeadlines(severity, created) {
      const [r, s] = SLA_POLICY[severity];
      return [addMinutes(created, r), addMinutes(created, s)];
    }
    checkSla(inc, now) {
      if (inc.resolved_at) return inc.resolved_at > inc.resolution_due_at;
      const breached = now > inc.resolution_due_at;
      if (breached && !inc.is_breached) {
        inc.is_breached = true;
        this.audit(inc, now, "sla-engine", "SLA_BREACH", inc.status, inc.status);
      }
      return breached;
    }
    resolveOwner() {
      if (!this.engineers.length) return null;
      return this.engineers.slice().sort((a, b) =>
        a.open_incidents - b.open_incidents || (a.engineer_id < b.engineer_id ? -1 : 1))[0];
    }
    transition(inc, next, at, actor = "engineer") {
      if (!TRANSITIONS[inc.status].includes(next))
        throw new InvalidTransitionError(`${inc.status} -> ${next} is not a permitted transition`);
      this.changeStatus(inc, next, at, actor);
      if (next === S.RESOLVED) {
        inc.resolved_at = at;
        if (inc.assignee) inc.assignee.open_incidents -= 1;
      } else if (next === S.REOPENED) {          // DEF-01 / DEF-02 fix
        inc.resolved_at = null;
        if (inc.assignee) inc.assignee.open_incidents += 1;
      }
      return inc;
    }
    changeStatus(inc, next, at, actor) {
      const old = inc.status;
      inc.status = next;
      this.audit(inc, at, actor, "STATUS_CHANGE", old, next);
    }
    static mttrMinutes(inc) {
      return inc.resolved_at ? (inc.resolved_at - inc.created_at) / 60000 : null;
    }
    audit(inc, at, actor, action, from, to) {
      const prev = inc.audit.length ? inc.audit[inc.audit.length - 1].hash : "0".repeat(64);
      const payload = [prev, isoformat(at), actor, action, from || "-", to || "-"].join("|");
      inc.audit.push({ at, actor, action, from_status: from, to_status: to, prev_hash: prev, hash: sha256(payload) });
    }
  }

  // ------------------------------------------------------- port of telemetry
  const RESOURCES = [
    ["vpn-tunnel-01", "VPN tunnel", "packet loss", "%", "VPN_TUNNEL_DOWN", "High", 0.5, 0.2, 20, 100, 4],
    ["vm-app-03", "Virtual machine", "CPU", "%", "HIGH_CPU", "Medium", 40, 4, 90, 97.2, 72],
    ["api-payments", "REST API", "p95 latency", "ms", "API_OUTAGE", "Critical", 120, 12, 2000, 30000, 420],
    ["db-primary", "Database", "connection wait", "ms", "DB_CONN_TIMEOUT", "High", 8, 1.5, 1000, 5000, 40],
    ["container-worker-02", "Container", "memory", "%", "CONTAINER_CRASH", "High", 55, 3, 95, 99, 78],
    ["auth-gateway", "Auth service", "failed logins", "/min", "SUSPICIOUS_LOGIN", "High", 2, 1, 50, 140, 15],
  ].map(([resource_id, kind, metric, unit, anomaly_type, severity, baseline, spread, threshold, outage_value, subtle_value]) =>
    ({ resource_id, kind, metric, unit, anomaly_type, severity, baseline, spread, threshold, outage_value, subtle_value }));
  const PROFILES = Object.fromEntries(RESOURCES.map((p) => [p.resource_id, p]));
  const HEALTHY = "healthy", OUTAGE = "outage", SUBTLE = "subtle";

  function gauss(mu, sigma) {
    let u = 0, v = 0;
    while (u === 0) u = Math.random();
    while (v === 0) v = Math.random();
    return mu + sigma * Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
  }
  function reading(p, mode) {
    let v;
    if (mode === OUTAGE) v = gauss(p.outage_value, p.outage_value * 0.01);
    else if (mode === SUBTLE) v = gauss(p.subtle_value, p.spread);
    else {
      v = gauss(p.baseline, p.spread);
      if (Math.random() < 0.01) v += (2 + Math.random()) * p.spread;
    }
    return Math.round(Math.max(v, 0) * 100) / 100;
  }

  // ---------------------------------------------- exported Isolation Forest
  class AnomalyScorer {
    constructor(model) {
      this.model = model;
      this.window = model.window;
      this.streak = model.streak;
      this.threshold = model.threshold;
      this.stats = model.stats;
    }
    static features(window, mean, std) {
      const z = window.map((v) => (v - mean) / std);
      const sorted = z.slice().sort((a, b) => a - b);
      return [z[z.length - 1], sorted[Math.floor(sorted.length / 2)], sorted[0]];
    }
    scoreRow(x) {
      x = x.map(Math.fround);   // scikit-learn compares features as 32-bit floats
      let total = 0;
      for (const nodes of this.model.trees) {
        let i = 0;
        while (nodes[i].length === 4) {
          const [f, thr, l, r] = nodes[i];
          i = x[f] <= thr ? l : r;
        }
        total += nodes[i][0];
      }
      return Math.pow(2, -(total / this.model.trees.length) / this.model.c);
    }
    score(rid, hist) {
      if (hist.length < this.window) return null;
      const [m, s] = this.stats[rid];
      return this.scoreRow(AnomalyScorer.features(hist.slice(-this.window), m, s));
    }
    isAnomalous(score) { return score !== null && score > this.threshold; }
    explain(rid, hist) {
      const [m, s] = this.stats[rid];
      const [level, , low] = AnomalyScorer.features(hist.slice(-this.window), m, s);
      const sd = (x) => (x >= 0 ? "+" : "") + x.toFixed(1);
      return `latest reading ${fmtG(hist[hist.length - 1])} is ${sd(level)} standard deviations ` +
        `from this resource's learned normal of ${m.toFixed(2)}; even the lowest of the last ` +
        `${this.window} readings is ${sd(low)} sd, so this is sustained, not a one-off spike`;
    }
  }

  // --------------------------------------------------------- port of server
  const USERS = {
    admin: { name: "System Administrator", role: "Administrator", engineer: null },
    manager: { name: "Incident Manager", role: "Incident Manager", engineer: null },
    smenon: { name: "S. Menon", role: "Engineer", engineer: "E02" },
    riyer: { name: "R. Iyer", role: "Engineer", engineer: "E01" },
    kdesh: { name: "K. Deshpande", role: "Engineer", engineer: "E03" },
    auditor: { name: "Compliance Auditor", role: "Viewer", engineer: null },
  };
  const ROOT_CAUSES = ["Configuration change", "Capacity exhausted", "Software defect",
    "Network fault", "Third-party outage", "Security event", "Other"];
  const NEXT_ACTION = {
    [S.ASSIGNED]: [S.ACKNOWLEDGED, "Acknowledge"], [S.ACKNOWLEDGED]: [S.IN_PROGRESS, "Start work"],
    [S.ESCALATED]: [S.IN_PROGRESS, "Start work"], [S.REOPENED]: [S.IN_PROGRESS, "Start work"],
    [S.IN_PROGRESS]: [S.RESOLVED, "Resolve"], [S.RESOLVED]: [S.CLOSED, "Close"],
  };
  const LABELS = { [S.ACKNOWLEDGED]: "Acknowledge", [S.IN_PROGRESS]: "Start work", [S.RESOLVED]: "Resolve",
    [S.CLOSED]: "Close", [S.REOPENED]: "Reopen", [S.ESCALATED]: "Escalate" };
  const ROLE_TRANSITIONS = {
    "Administrator": new Set(Object.values(S)),
    "Incident Manager": new Set([S.ESCALATED, S.CLOSED, S.REOPENED]),
    "Engineer": new Set([S.ACKNOWLEDGED, S.IN_PROGRESS, S.RESOLVED, S.ESCALATED]),
    "Viewer": new Set(),
  };

  class HttpError extends Error {
    constructor(status, message, fields) { super(message); this.status = status; this.fields = fields; }
  }

  class Platform {
    constructor(scorer) { this.scorer = scorer; this.reset(); }
    reset() {
      this.service = new IncidentService([
        { engineer_id: "E01", name: "R. Iyer", team: "Network", open_incidents: 2 },
        { engineer_id: "E02", name: "S. Menon", team: "Platform", open_incidents: 0 },
        { engineer_id: "E03", name: "K. Deshpande", team: "Backend", open_incidents: 1 },
      ]);
      this.faults = {};
      this.history = {}; this.scores = {}; this.scoreHistory = {}; this.ruleCount = {}; this.aiCount = {};
      for (const p of RESOURCES) {
        const id = p.resource_id;
        this.history[id] = []; this.scores[id] = null; this.scoreHistory[id] = []; this.ruleCount[id] = 0; this.aiCount[id] = 0;
      }
      this.meta = {};
      this.offset = 0;
      this.log = [];
      this.pending = [];
      this.aiStats = { scored: 0, flagged: 0, incidents: 0 };
    }
    user(id) {
      if (!USERS[id]) throw new HttpError(401, "sign in required");
      return { id, ...USERS[id] };
    }
    owns(u, inc) { return inc.assignee && inc.assignee.engineer_id === u.engineer; }
    canTransition(u, inc, t) {
      if (!TRANSITIONS[inc.status].includes(t)) return false;
      if (!ROLE_TRANSITIONS[u.role].has(t)) return false;
      return u.role !== "Engineer" || this.owns(u, inc);
    }
    canNote(u, inc) {
      return u.role === "Administrator" || u.role === "Incident Manager" ||
        (u.role === "Engineer" && this.owns(u, inc));
    }
    requireAdmin(u) { if (u.role !== "Administrator") throw new HttpError(403, "administrator role required"); }
    now() { return new Date(Date.now() + this.offset); }
    advanceClock(min) { this.offset += min * 60000; this.addLog("CLOCK", `simulated clock advanced ${fmtG(min)} min`); }
    addLog(stage, msg) { this.log.push({ t: hms(this.now()), stage, msg }); this.log = this.log.slice(-200); }

    injectFault(rid, kind = OUTAGE) {
      if (!PROFILES[rid]) throw new HttpError(404, "unknown resource or incident");
      if (kind !== OUTAGE && kind !== SUBTLE) throw new HttpError(400, "fault kind must be outage or subtle");
      this.faults[rid] = kind;
      this.addLog("SIM", `${kind === OUTAGE ? "outage" : "gradual degradation"} injected on ${rid}`);
    }
    tick() {
      for (const inc of this.pending)
        this.addLog("NOTIFY", `${inc.incident_id} alert delivered to ${inc.assignee ? inc.assignee.name : "unassigned queue"}`);
      this.pending = [];
      for (const p of RESOURCES) {
        const rid = p.resource_id, v = reading(p, this.faults[rid] || HEALTHY), h = this.history[rid];
        h.push(v);
        if (h.length > 40) h.splice(0, h.length - 40);
        this.ruleEngine(p, v);
        this.aiDetector(p, h);
      }
      for (const inc of this.service.incidents) {
        const was = inc.is_breached;
        if (OPEN.has(inc.status) && this.service.checkSla(inc, this.now()) && !was)
          this.addLog("SLA", `${inc.incident_id} resolution SLA breached, escalation sent to on-call lead`);
      }
    }
    ruleEngine(p, v) {
      const rid = p.resource_id;
      if (v <= p.threshold) { this.ruleCount[rid] = 0; return; }
      const n = ++this.ruleCount[rid];
      if (n < 2) this.addLog("MONITOR", `${rid} ${p.anomaly_type} reading ${fmtG(v)} breaches threshold ${fmtG(p.threshold)} (${n}/2)`);
      else if (n === 2) {
        this.addLog("MONITOR", `${rid} rule ${p.anomaly_type} fired`);
        this.create({ resource_id: rid, anomaly_type: p.anomaly_type, observed_value: v, severity: p.severity, detected_at: this.now() },
          "detection-engine", "rule");
      }
    }
    aiDetector(p, h) {
      const rid = p.resource_id, sc = this.scorer.score(rid, h);
      this.scores[rid] = sc;
      if (sc === null) return;
      const sh = this.scoreHistory[rid];
      sh.push(Math.round(sc * 10000) / 10000);
      if (sh.length > 40) sh.splice(0, sh.length - 40);
      this.aiStats.scored++;
      if (!this.scorer.isAnomalous(sc)) { this.aiCount[rid] = 0; return; }
      this.aiStats.flagged++;
      if (++this.aiCount[rid] !== this.scorer.streak) return;
      if (this.service.incidents.some((i) => i.resource_id === rid && OPEN.has(i.status))) return;
      const thr = this.scorer.threshold;
      this.addLog("AI", `${rid} anomaly score ${sc.toFixed(3)} > ${thr.toFixed(3)} for ${this.scorer.streak} readings; no rule fired`);
      const inc = this.create({ resource_id: rid, anomaly_type: "ML_ANOMALY", observed_value: h[h.length - 1],
        severity: Severity.MEDIUM, detected_at: this.now() }, "ai-anomaly-detector", "ai",
        { score: +sc.toFixed(3), threshold: +thr.toFixed(3), reason: this.scorer.explain(rid, h),
          metric: p.metric, unit: p.unit, threshold_rule: p.threshold });
      if (inc) this.aiStats.incidents++;
    }
    create(e, actor, source = "rule", ai = null) {
      const before = this.service.incidents.length;
      const inc = this.service.createIncident(e, actor);
      if (this.service.incidents.length > before) {
        this.meta[inc.incident_id] = { source, ai, notes: [], resolution: null };
        this.addLog("INCIDENT", `${inc.incident_id} created, ${inc.severity}, assigned to ` +
          `${inc.assignee ? inc.assignee.name : "none"}${source === "ai" ? " [AI-detected]" : ""}`);
        this.addLog("AUDIT", `${inc.incident_id} ${inc.audit.length} audit entries written`);
        this.pending.push(inc);
      } else this.addLog("INCIDENT", `duplicate event linked to ${inc.incident_id}`);
      return inc;
    }
    incident(id) {
      const inc = this.service.incidents.find((i) => i.incident_id === id);
      if (!inc) throw new HttpError(404, "unknown resource or incident");
      return inc;
    }
    submitEvent(d) {
      const sev = d.severity || "Medium";
      if (!Object.values(Severity).includes(sev)) throw new HttpError(400, `'${sev}' is not a valid Severity`);
      const value = Number(d.observed_value ?? 0);
      if (Number.isNaN(value)) throw new HttpError(400, "could not convert string to float");
      return this.create({ resource_id: String(d.resource_id ?? ""), anomaly_type: String(d.anomaly_type ?? ""),
        observed_value: value, severity: sev, detected_at: this.now() }, "admin-console", "manual");
    }
    transition(u, id, to) {
      const inc = this.incident(id);
      if (!TRANSITIONS[inc.status].includes(to)) throw new HttpError(400, `${inc.status} -> ${to} is not a permitted transition`);
      if (!this.canTransition(u, inc, to)) throw new HttpError(403, `${u.role} may not move this incident to ${to}`);
      if (to === S.RESOLVED) throw new HttpError(400, "resolution details required: use the Resolve form");
      this.service.transition(inc, to, this.now(), u.name);
      this.addLog("AUDIT", `${id} -> ${inc.status} by ${u.name}`);
    }
    resolve(u, id, category, fix) {
      const inc = this.incident(id);
      if (!this.canTransition(u, inc, S.RESOLVED)) {
        if (!TRANSITIONS[inc.status].includes(S.RESOLVED)) throw new HttpError(400, `${inc.status} -> Resolved is not a permitted transition`);
        throw new HttpError(403, `${u.role} may not resolve this incident`);
      }
      const errors = {};
      if (!ROOT_CAUSES.includes(category)) errors.category = "choose a root cause category";
      if ((fix || "").trim().length < 10) errors.fix = "describe the fix in at least 10 characters";
      if (Object.keys(errors).length) throw new HttpError(400, Object.values(errors).join("; "), errors);
      this.service.transition(inc, S.RESOLVED, this.now(), u.name);
      this.meta[id].resolution = { category, fix: fix.trim(), by: u.name, t: hms(this.now()) };
      delete this.faults[inc.resource_id];
      this.aiCount[inc.resource_id] = 0;
      this.addLog("AUDIT", `${id} -> Resolved by ${u.name} (${category})`);
    }
    addNote(u, id, text) {
      const inc = this.incident(id);
      if (!this.canNote(u, inc)) throw new HttpError(403, `${u.role} may not add notes to this incident`);
      text = (text || "").trim();
      if (!text) throw new HttpError(400, "note cannot be empty", { note: "note cannot be empty" });
      this.meta[id].notes.push({ t: hms(this.now()), by: u.name, text: text.slice(0, 1000) });
    }
    state(u) {
      const inc = this.service.incidents;
      const mttrs = inc.map(IncidentService.mttrMinutes).filter((m) => m !== null);
      return {
        me: u, now: isoSeconds(this.now()),
        resources: RESOURCES.map((p) => {
          const rid = p.resource_id, sc = this.scores[rid];
          return { id: rid, type: p.kind, metric: p.metric, unit: p.unit, anomaly: p.anomaly_type,
            threshold: p.threshold, baseline: +this.scorer.stats[rid][0].toFixed(2),
            spread: +this.scorer.stats[rid][1].toFixed(3),
            fault: this.faults[rid] || null, faulted: rid in this.faults, history: this.history[rid].slice(), score_history: this.scoreHistory[rid].slice(),
            score: sc === null ? null : +sc.toFixed(3), ai_flag: this.scorer.isAnomalous(sc) };
        }),
        incidents: inc.slice().reverse().map((i) => this.view(i, u)),
        engineers: this.service.engineers.map((e) => ({ id: e.engineer_id, name: e.name, team: e.team, open: e.open_incidents })),
        metrics: {
          open: inc.filter((i) => OPEN.has(i.status)).length,
          healthy: RESOURCES.length - Object.keys(this.faults).length,
          breached: inc.filter((i) => i.is_breached).length,
          ai: Object.values(this.meta).filter((m) => m.source === "ai").length,
          mttr: mttrs.length ? Math.round(mttrs.reduce((a, b) => a + b, 0) / mttrs.length * 100) / 100 : null,
        },
        sla_policy: Object.entries(SLA_POLICY).map(([severity, [response, resolution]]) => ({ severity, response, resolution })),
        root_causes: ROOT_CAUSES,
        ai: { threshold: +this.scorer.threshold.toFixed(3), streak: this.scorer.streak, ...this.aiStats },
        log: this.log.slice(-80),
      };
    }
    view(inc, u) {
      const nxt = NEXT_ACTION[inc.status];
      const action = nxt && this.canTransition(u, inc, nxt[0]) ? { to: nxt[0], label: nxt[1] } : null;
      const actions = TRANSITIONS[inc.status].slice().sort()
        .filter((t) => LABELS[t] && this.canTransition(u, inc, t)).map((t) => ({ to: t, label: LABELS[t] }));
      const m = this.meta[inc.incident_id] || { source: "rule", ai: null, notes: [], resolution: null };
      return {
        id: inc.incident_id, resource: inc.resource_id, anomaly: inc.anomaly_type, severity: inc.severity,
        status: inc.status, open: OPEN.has(inc.status), assignee: inc.assignee ? inc.assignee.name : null,
        created: isoSeconds(inc.created_at), response_due: isoSeconds(inc.response_due_at),
        resolution_due: isoSeconds(inc.resolution_due_at),
        acknowledged: inc.audit.some((a) => a.to_status === S.ACKNOWLEDGED),
        breached: inc.is_breached, events: inc.linked_events.length, mttr: IncidentService.mttrMinutes(inc),
        action, actions, can_note: this.canNote(u, inc), source: m.source, ai: m.ai, notes: m.notes.slice(),
        resolution: m.resolution,
        audit: inc.audit.map((a) => ({ t: hms(a.at), actor: a.actor, action: a.action, from: a.from_status || "-",
          to: a.to_status || "-", hash: a.hash.slice(0, 12) })),
      };
    }
  }

  // ------------------------------------------- same API as console/server.py
  class LocalBackend {
    constructor(model, tickMs = 750) {
      this.platform = new Platform(new AnomalyScorer(model));
      this.timer = setInterval(() => this.platform.tick(), tickMs);
      this.mode = "standalone";
    }
    async request(method, path, body, userId) {
      const pl = this.platform;
      try {
        if (method === "GET" && path === "/api/users") return { ok: true, status: 200, data: Object.entries(USERS).map(([id, v]) => ({ id, ...v })) };
        const u = pl.user(userId || "");
        if (method === "GET" && path === "/api/state") return { ok: true, status: 200, data: pl.state(u) };
        const parts = path.split("/");
        if (path === "/api/fault") { pl.requireAdmin(u); pl.injectFault(body.resource_id, body.kind || OUTAGE); }
        else if (path === "/api/events") {
          pl.requireAdmin(u);
          try { return { ok: true, status: 201, data: { incident: pl.submitEvent(body).incident_id } }; }
          catch (e) { if (e instanceof ValidationError) throw new HttpError(400, e.message); throw e; }
        }
        else if (path.startsWith("/api/incidents/") && parts.length === 5) {
          const [id, verb] = [parts[3], parts[4]];
          if (verb === "transition") pl.transition(u, id, body.to);
          else if (verb === "resolve") pl.resolve(u, id, body.category, body.fix);
          else if (verb === "notes") pl.addNote(u, id, body.text);
          else throw new HttpError(404, "not found");
        }
        else if (path === "/api/clock") { pl.requireAdmin(u); pl.advanceClock(Number(body.minutes)); }
        else if (path === "/api/reset") { pl.requireAdmin(u); pl.reset(); }
        else throw new HttpError(404, "not found");
        return { ok: true, status: 200, data: { ok: true } };
      } catch (e) {
        if (e instanceof HttpError) return { ok: false, status: e.status, data: { error: e.message, fields: e.fields } };
        if (e instanceof ValidationError || e instanceof InvalidTransitionError) return { ok: false, status: 400, data: { error: e.message } };
        throw e;
      }
    }
  }

  root.CIRPEngine = { IncidentService, AnomalyScorer, Platform, LocalBackend, sha256, isoformat, RESOURCES, Status, Severity };
  if (typeof module !== "undefined") module.exports = root.CIRPEngine;
})(typeof window !== "undefined" ? window : globalThis);
