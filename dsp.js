/* Motore di analisi della dizione — porting in JavaScript di analisi.py
 * (server "dizione" del PC). Stessi criteri: formanti con LPC di Burg come
 * Praat, nuclei vocalici dai picchi di intensità, taratura sulle tue vocali.
 * Funziona nel browser e in Node (per i test).
 */
(function (root) {
  'use strict';

  const VOCALI = new Set('aeiouàáèéìíòóùú');
  const ACCENTI = { 'à': 'a', 'á': 'a', 'è': 'è', 'é': 'é', 'ì': 'i', 'í': 'i', 'ò': 'ò', 'ó': 'ó', 'ù': 'u', 'ú': 'u' };
  const CATEGORIE = ['i', 'é', 'è', 'a', 'ò', 'ó', 'u'];
  const COPPIE_APERTURA = { 'é': ['é', 'è'], 'è': ['é', 'è'], 'ó': ['ó', 'ò'], 'ò': ['ó', 'ò'] };
  const PROFILI_VOCE = {
    uomo: { maxFormante: 5000, f0min: 60, f0max: 300 },
    donna: { maxFormante: 5500, f0min: 100, f0max: 500 },
  };
  const SOGLIA_CHIUSA = 0.35, SOGLIA_APERTA = 0.65;
  const RAPPORTO_DOPPIA_OK = 1.6, RAPPORTO_DOPPIA_DEBOLE = 1.3;
  const PASSO = 0.005; // s tra i frame

  const bark = (f) => 26.81 * f / (1960 + f) - 0.53;
  const senzaAccenti = (s) => s.normalize('NFD').replace(/[̀-ͯ]/g, '').normalize('NFC');
  const mediana = (v) => {
    const a = v.filter((x) => Number.isFinite(x)).sort((p, q) => p - q);
    if (!a.length) return NaN;
    const m = a.length >> 1;
    return a.length % 2 ? a[m] : (a[m - 1] + a[m]) / 2;
  };
  const percentile = (arr, p) => {
    const a = Array.from(arr).sort((x, y) => x - y);
    if (!a.length) return NaN;
    const k = (a.length - 1) * p / 100, f = Math.floor(k), c = Math.min(a.length - 1, f + 1);
    return a[f] + (a[c] - a[f]) * (k - f);
  };
  const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);

  // ------------------------------------------------------------ parole
  function analizzaTesto(testo) {
    const w = testo.trim().toLowerCase().normalize('NFC');
    const gruppi = [];
    let i = 0;
    while (i < w.length) {
      if (VOCALI.has(w[i])) {
        let j = i;
        while (j < w.length && VOCALI.has(w[j])) j++;
        gruppi.push([i, j]);
        i = j;
      } else i++;
    }
    let attesa = null, idx = null;
    for (let k = 0; k < gruppi.length && idx === null; k++) {
      for (const ch of w.slice(gruppi[k][0], gruppi[k][1])) {
        if (ACCENTI[ch]) { attesa = ACCENTI[ch]; idx = k; break; }
      }
    }
    const n = gruppi.length;
    const dopo = idx === null ? (n >= 2 ? 1 : 0) : n - 1 - idx;
    return { testo: testo.trim(), attesa, sillabe: n, dopoTonica: dopo };
  }

  // ------------------------------------------------------------ segnale
  function ricampiona(x, fsIn, fsOut) {
    if (fsIn === fsOut) return Float64Array.from(x);
    const ratio = fsIn / fsOut;
    const n = Math.floor(x.length / ratio);
    const y = new Float64Array(n);
    const fc = 0.5 * Math.min(1, 1 / ratio) * 0.95;      // frequenza di taglio normalizzata (su fsIn)
    const half = Math.ceil(16 * Math.max(1, ratio));       // semi-lunghezza del filtro in campioni d'ingresso
    for (let k = 0; k < n; k++) {
      const t = k * ratio;
      const c = Math.floor(t);
      let s = 0, ws = 0;
      for (let j = c - half + 1; j <= c + half; j++) {
        if (j < 0 || j >= x.length) continue;
        const d = t - j;
        const sinc = d === 0 ? 2 * fc : Math.sin(2 * Math.PI * fc * d) / (Math.PI * d);
        const win = 0.5 + 0.5 * Math.cos(Math.PI * d / half);
        const h = sinc * win;
        s += x[j] * h; ws += h;
      }
      y[k] = ws ? s / ws : 0;
    }
    return y;
  }

  function livelli(x) {
    let picco = 0, clip = 0;
    for (let i = 0; i < x.length; i++) {
      const a = Math.abs(x[i]);
      if (a > picco) picco = a;
      if (a > 0.99) clip++;
    }
    return { piccoDbfs: picco > 0 ? 20 * Math.log10(picco) : -120, clipping: 100 * clip / Math.max(1, x.length) };
  }

  // ------------------------------------------------------------ tracce
  /* Intensità (dB, finestra gaussiana ~ 32 ms efficaci come Praat con 100 Hz)
   * e sonorità (autocorrelazione normalizzata) a passi di 5 ms. */
  function calcolaTracce(x10k, fs, profilo) {
    const n = x10k.length;
    const passo = Math.round(PASSO * fs);
    const lungI = Math.round(0.064 * fs), sigma = lungI / 6;
    const wI = new Float64Array(lungI);
    let sw = 0;
    for (let i = 0; i < lungI; i++) { const d = i - (lungI - 1) / 2; wI[i] = Math.exp(-0.5 * (d / sigma) ** 2); sw += wI[i]; }
    const lagMin = Math.floor(fs / profilo.f0max), lagMax = Math.ceil(fs / profilo.f0min);
    const lungP = Math.round(3 / profilo.f0min * fs);
    let piccoAss = 0;
    for (let i = 0; i < n; i++) piccoAss = Math.max(piccoAss, Math.abs(x10k[i]));
    const nFrame = Math.max(0, Math.floor((n - 1) / passo) + 1);
    const t = new Float64Array(nFrame), db = new Float64Array(nFrame);
    const sonoro = new Uint8Array(nFrame);
    const lungZ = Math.round(0.03 * fs);
    let dbMax = -Infinity;
    const zcr = new Float64Array(nFrame);
    for (let f = 0; f < nFrame; f++) {
      const c = f * passo;
      t[f] = c / fs;
      // passaggi per lo zero (alti nelle fricative sorde come s, f)
      let zc = 0, zn = 0;
      for (let k = Math.max(1, c - (lungZ >> 1)); k < Math.min(n, c + (lungZ >> 1)); k++) {
        if ((x10k[k] >= 0) !== (x10k[k - 1] >= 0)) zc++;
        zn++;
      }
      zcr[f] = zn ? zc / zn * fs / 2 : 0;
      // intensità
      let e = 0, ww = 0;
      const i0 = c - (lungI >> 1);
      for (let i = 0; i < lungI; i++) {
        const k = i0 + i;
        if (k < 0 || k >= n) continue;
        e += wI[i] * x10k[k] * x10k[k]; ww += wI[i];
      }
      db[f] = 10 * Math.log10((ww ? e / ww : 0) / 4e-10 + 1e-30);
      if (db[f] > dbMax) dbMax = db[f];
      // sonorità
      const a = c - (lungP >> 1), b = a + lungP;
      if (a < 0 || b + lagMax >= n) continue;
      let amp = 0;
      for (let k = a; k < b; k++) amp = Math.max(amp, Math.abs(x10k[k]));
      if (amp < 0.03 * piccoAss) continue;
      let e0 = 0;
      for (let k = a; k < b; k++) e0 += x10k[k] * x10k[k];
      let migliore = 0;
      for (let lag = lagMin; lag <= lagMax; lag++) {
        let r = 0, e1 = 0;
        for (let k = a; k < b; k++) { r += x10k[k] * x10k[k + lag]; e1 += x10k[k + lag] * x10k[k + lag]; }
        const v = r / Math.sqrt(e0 * e1 + 1e-30);
        if (v > migliore) migliore = v;
      }
      sonoro[f] = migliore > 0.45 ? 1 : 0;
    }
    // vocali con voce irregolare (es. finali "scricchiolate"): forti e senza rumore di fricativa
    for (let f = 0; f < nFrame; f++) if (!sonoro[f] && zcr[f] < 1500 && db[f] > dbMax - 30) sonoro[f] = 1;
    // chiude i buchi brevi di sonorità (≤ 30 ms)
    let i = 0;
    while (i < nFrame) {
      if (!sonoro[i]) {
        let j = i;
        while (j < nFrame && !sonoro[j]) j++;
        if (i > 0 && j < nFrame && j - i <= 6) sonoro.fill(1, i, j);
        i = j;
      } else i++;
    }
    return { t, db, sonoro };
  }

  // ------------------------------------------------------------ formanti (Burg, come Praat)
  function burg(x, m) {
    const n = x.length;
    const d = new Float64Array(m + 1), wkm = new Float64Array(m + 1);
    const wk1 = new Float64Array(n), wk2 = new Float64Array(n);
    for (let j = 0; j < n - 1; j++) { wk1[j] = x[j]; wk2[j] = x[j + 1]; }
    for (let k = 1; k <= m; k++) {
      let num = 0, den = 0;
      for (let j = 0; j < n - k; j++) { num += wk1[j] * wk2[j]; den += wk1[j] * wk1[j] + wk2[j] * wk2[j]; }
      if (den <= 0) return null;
      d[k] = 2 * num / den;
      for (let i = 1; i < k; i++) d[i] = wkm[i] - d[k] * wkm[k - i];
      if (k === m) break;
      for (let i = 1; i <= k; i++) wkm[i] = d[i];
      for (let j = 0; j < n - k - 1; j++) {
        wk1[j] -= wkm[k] * wk2[j];
        wk2[j] = wk2[j + 1] - wkm[k] * wk1[j + 1];
      }
    }
    return d; // x[n] ≈ Σ d[k]·x[n−k]
  }

  // radici di z^m − d1 z^(m−1) − … − dm con il metodo di Aberth–Ehrlich
  function radici(d, m) {
    const c = [1]; for (let k = 1; k <= m; k++) c.push(-d[k]);
    const val = (zr, zi) => { // p(z) e p'(z)
      let pr = 1, pi = 0, dr = 0, di = 0;
      for (let k = 1; k <= m; k++) {
        const ndr = dr * zr - di * zi + pr, ndi = dr * zi + di * zr + pi;
        dr = ndr; di = ndi;
        const npr = pr * zr - pi * zi + c[k], npi = pr * zi + pi * zr;
        pr = npr; pi = npi;
      }
      return [pr, pi, dr, di];
    };
    const zr = new Float64Array(m), zi = new Float64Array(m);
    for (let k = 0; k < m; k++) { const a = 2 * Math.PI * (k + 0.25) / m + 0.4; zr[k] = 0.9 * Math.cos(a); zi[k] = 0.9 * Math.sin(a); }
    for (let it = 0; it < 300; it++) {
      let mosso = 0;
      for (let k = 0; k < m; k++) {
        const [pr, pi, dr, di] = val(zr[k], zi[k]);
        const dd = dr * dr + di * di;
        if (dd === 0) continue;
        const qr = (pr * dr + pi * di) / dd, qi = (pi * dr - pr * di) / dd; // p/p'
        let sr = 0, si = 0;
        for (let j = 0; j < m; j++) {
          if (j === k) continue;
          const ar = zr[k] - zr[j], ai = zi[k] - zi[j], aa = ar * ar + ai * ai || 1e-30;
          sr += ar / aa; si += -ai / aa;
        }
        // w = q / (1 − q·s)
        const br = 1 - (qr * sr - qi * si), bi = -(qr * si + qi * sr), bb = br * br + bi * bi || 1e-30;
        const wr = (qr * br + qi * bi) / bb, wi = (qi * br - qr * bi) / bb;
        zr[k] -= wr; zi[k] -= wi;
        mosso = Math.max(mosso, Math.hypot(wr, wi));
      }
      if (mosso < 1e-12) break;
    }
    return [zr, zi];
  }

  function formantiFrame(y, fs, centro, profilo) {
    const lung = Math.round(0.05 * fs); // finestra fisica = 2 × 25 ms
    const i0 = Math.round(centro * fs) - (lung >> 1);
    if (i0 < 0 || i0 + lung > y.length) return [NaN, NaN, NaN];
    const fr = new Float64Array(lung);
    const bordo = Math.exp(-12);
    for (let i = 0; i < lung; i++) {
      const d = i - (lung - 1) / 2;
      const w = (Math.exp(-48 * d * d / ((lung + 1) * (lung + 1))) - bordo) / (1 - bordo);
      fr[i] = y[i0 + i] * w;
    }
    const m = 10;
    const d = burg(fr, m);
    if (!d) return [NaN, NaN, NaN];
    const [zr, zi] = radici(d, m);
    const out = [];
    for (let k = 0; k < m; k++) {
      let r = zr[k], im = zi[k];
      let mod = Math.hypot(r, im);
      if (mod > 1) { r /= mod * mod; im /= mod * mod; mod = 1 / mod; } // riflette dentro il cerchio unitario
      if (im <= 0) continue;
      const f = Math.atan2(im, r) * fs / (2 * Math.PI);
      if (f > 50 && f < profilo.maxFormante - 50) out.push(f);
    }
    out.sort((a, b) => a - b);
    return [out[0] ?? NaN, out[1] ?? NaN, out[2] ?? NaN];
  }

  // segnale per le formanti: ricampionato a 2×max formante e con pre-enfasi da 50 Hz
  function preparaFormanti(x, fs, profilo) {
    const fsF = 2 * profilo.maxFormante;
    const y = ricampiona(x, fs, fsF);
    const a = Math.exp(-2 * Math.PI * 50 / fsF);
    for (let i = y.length - 1; i > 0; i--) y[i] -= a * y[i - 1];
    return { y, fs: fsF };
  }

  function misuraFormanti(pf, a, b, profilo) {
    const d = b - a;
    const tempi = d < 0.04 ? [a + d / 2] : Array.from({ length: 7 }, (_, i) => a + 0.25 * d + i * (0.5 * d) / 6);
    const v = [[], [], []];
    for (const t of tempi) {
      const f = formantiFrame(pf.y, pf.fs, t, profilo);
      for (let k = 0; k < 3; k++) v[k].push(f[k]);
    }
    return v.map(mediana);
  }

  // ------------------------------------------------------------ segmentazione
  function trovaSegmenti(tr, unione = 0.30, durataMin = 0.10, sogliaRel = 25) {
    const picco = percentile(tr.db, 99.5), rumore = percentile(tr.db, 10);
    const soglia = Math.max(picco - sogliaRel, rumore + 8);
    const seg = [];
    let i = 0;
    const n = tr.db.length;
    while (i < n) {
      if (tr.db[i] > soglia) {
        let j = i;
        while (j < n && tr.db[j] > soglia) j++;
        seg.push([tr.t[i], tr.t[j - 1]]);
        i = j;
      } else i++;
    }
    const uniti = [];
    for (const s of seg) {
      if (uniti.length && s[0] - uniti[uniti.length - 1][1] < unione) uniti[uniti.length - 1][1] = s[1];
      else uniti.push([s[0], s[1]]);
    }
    return uniti.filter(([a, b]) => b - a >= durataMin);
  }

  function assegnaAParole(segmenti, nParole, finestre) {
    const out = new Array(nParole).fill(null);
    if (finestre) {
      const gruppi = Array.from({ length: nParole }, () => []);
      for (const [a, b] of segmenti) {
        let migliore = 0;
        finestre.forEach(([wa], k) => { if (wa + 0.10 <= a) migliore = k; });
        if (a > finestre[migliore][1] + 1.0) continue;
        gruppi[migliore].push([a, b]);
      }
      gruppi.forEach((g, k) => { if (g.length) out[k] = [Math.min(...g.map((x) => x[0])), Math.max(...g.map((x) => x[1]))]; });
      return out;
    }
    segmenti.slice(0, nParole).forEach((s, k) => { out[k] = s; });
    return out;
  }

  const indici = (tr, a, b) => { const r = []; for (let i = 0; i < tr.t.length; i++) if (tr.t[i] >= a && tr.t[i] <= b) r.push(i); return r; };

  function trovaNuclei(tr, a, b, rel = 15, dip = 2) {
    const idx = indici(tr, a, b);
    if (idx.length < 3) return [];
    const seg = idx.map((i) => tr.db[i]);
    const top = Math.max(...seg);
    const sonoroVicino = (k) => {
      const g = idx[k];
      for (let i = Math.max(0, g - 4); i <= Math.min(tr.sonoro.length - 1, g + 4); i++) if (tr.sonoro[i]) return true;
      return seg[k] >= top - 6;
    };
    let picchi = [];
    for (let k = 1; k < seg.length - 1; k++) {
      if (seg[k] >= seg[k - 1] && seg[k] > seg[k + 1] && seg[k] > top - rel && sonoroVicino(k)) picchi.push(k);
    }
    let cambiato = true;
    while (cambiato && picchi.length > 1) {
      cambiato = false;
      for (let u = 0; u < picchi.length - 1; u++) {
        const p = picchi[u], q = picchi[u + 1];
        let m = Infinity;
        for (let k = p; k <= q; k++) m = Math.min(m, seg[k]);
        if (Math.min(seg[p], seg[q]) - m < dip) {
          picchi.splice(seg[p] < seg[q] ? u : u + 1, 1);
          cambiato = true;
          break;
        }
      }
    }
    return picchi.map((k) => idx[k]);
  }

  function confiniVocale(tr, p, prima, dopo) {
    const picco = tr.db[p];
    const livello = (lo, hi) => {
      let valle = picco;
      for (let k = lo; k <= hi; k++) valle = Math.min(valle, tr.db[k]);
      return picco - Math.min(Math.max(3, (picco - valle) / 2), 10);
    };
    const dentro = (k, liv) => tr.db[k] >= liv && (tr.sonoro[k] || tr.db[k] >= picco - 4);
    const livS = livello(prima, p);
    let i = p;
    while (i - 1 >= prima && dentro(i - 1, livS)) i--;
    const livD = livello(p, dopo);
    let j = p;
    while (j + 1 <= dopo && dentro(j + 1, livD)) j++;
    return [tr.t[i], tr.t[j]];
  }

  function minimo(tr, lo, hi) { let m = Infinity; for (let k = lo; k <= hi; k++) m = Math.min(m, tr.db[k]); return m; }

  function misuraParola(pf, tr, testo, intervallo, profilo) {
    const pw = analizzaTesto(testo);
    const m = { parola: testo, attesa: pw.attesa, inizio: null, fine: null, vocaleInizio: null, vocaleFine: null,
      f1: null, f2: null, f3: null, vocaleMs: null, consonanteMs: null, nuclei: 0, note: [],
      piuVicina: null, apertura: null, giudizio: null, esito: null };
    if (!intervallo) { m.note.push('non rilevata'); return m; }
    const [a, b] = intervallo;
    m.inizio = a; m.fine = b;
    const nuc = trovaNuclei(tr, a, b);
    const idxTok = indici(tr, a, b);
    const lo = idxTok[0], hi = idxTok[idxTok.length - 1];
    const prominenza = (k) => {
      const p = nuc[k], sx = k > 0 ? nuc[k - 1] : lo, dx = k + 1 < nuc.length ? nuc[k + 1] : hi;
      return tr.db[p] - Math.max(minimo(tr, sx, p), minimo(tr, p, dx));
    };
    while (pw.sillabe >= 1 && nuc.length > pw.sillabe) {
      let kmin = 0, pmin = Infinity;
      for (let k = 0; k < nuc.length; k++) { const v = prominenza(k); if (v < pmin) { pmin = v; kmin = k; } }
      nuc.splice(kmin, 1);
    }
    m.nuclei = nuc.length;
    if (!nuc.length) { m.note.push('nessuna vocale rilevata'); return m; }
    let k = nuc.length - 1 - pw.dopoTonica;
    if (k < 0 || k >= nuc.length) {
      k = 0; for (let u = 1; u < nuc.length; u++) if (tr.db[nuc[u]] > tr.db[nuc[k]]) k = u;
      m.note.push('tonica incerta');
    } else if (nuc.length < pw.sillabe && !pw.testo.includes(' ')) {
      m.note.push(`sillabe rilevate ${nuc.length} su ${pw.sillabe}`);
    }
    const prima = k > 0 ? nuc[k - 1] : lo, dopo = k + 1 < nuc.length ? nuc[k + 1] : hi;
    const [va, vb] = confiniVocale(tr, nuc[k], prima, dopo);
    m.vocaleInizio = va; m.vocaleFine = vb;
    m.vocaleMs = Math.round((vb - va) * 1000);
    if (k + 1 < nuc.length) {
      const dopo2 = k + 2 < nuc.length ? nuc[k + 2] : hi;
      const [na] = confiniVocale(tr, nuc[k + 1], nuc[k], dopo2);
      m.consonanteMs = Math.round(Math.max(0, na - vb) * 1000);
    }
    const [f1, f2, f3] = misuraFormanti(pf, va, vb, profilo);
    m.f1 = Number.isFinite(f1) ? Math.round(f1) : null;
    m.f2 = Number.isFinite(f2) ? Math.round(f2) : null;
    m.f3 = Number.isFinite(f3) ? Math.round(f3) : null;
    return m;
  }

  function prepara(x, fs, profilo) {
    const x10 = ricampiona(x, fs, 10000);
    return { tr: calcolaTracce(x10, 10000, profilo), pf: preparaFormanti(x, fs, profilo) };
  }

  /* Serie registrata di seguito (come sul PC). finestre: [inizio, fine] di ogni parola a schermo. */
  function misuraSerie(x, fs, parole, profilo, finestre = null) {
    const { tr, pf } = prepara(x, fs, profilo);
    const segmenti = trovaSegmenti(tr, finestre ? 0.45 : 0.35);
    const intervalli = assegnaAParole(segmenti, parole.length, finestre);
    return parole.map((p, i) => misuraParola(pf, tr, p, intervalli[i], profilo));
  }

  /* Una parola registrata da sola (uso sul telefono). */
  function misuraClip(x, fs, testo, profilo) {
    const { tr, pf } = prepara(x, fs, profilo);
    const segmenti = trovaSegmenti(tr, 0.45);
    let intervallo = null;
    if (segmenti.length) {
      // tiene i tratti con un picco entro 15 dB dal più forte (scarta rumori isolati)
      const piccoSeg = segmenti.map(([a, b]) => Math.max(...indici(tr, a, b).map((i) => tr.db[i])));
      const top = Math.max(...piccoSeg);
      const buoni = segmenti.filter((_, i) => piccoSeg[i] >= top - 15);
      intervallo = [Math.min(...buoni.map((s) => s[0])), Math.max(...buoni.map((s) => s[1]))];
    }
    const m = misuraParola(pf, tr, testo, intervallo, profilo);
    m.livelli = livelli(x);
    return m;
  }

  // ------------------------------------------------------------ taratura
  class Taratura {
    constructor(campioni = {}) { this.campioni = campioni; }
    aggiungi(cat, f1, f2) { (this.campioni[cat] = this.campioni[cat] || []).push([f1, f2]); }
    centroidiHz() {
      const out = {};
      for (const [c, v] of Object.entries(this.campioni)) {
        if (v.length) out[c] = [Math.round(mediana(v.map((x) => x[0]))), Math.round(mediana(v.map((x) => x[1]))), v.length];
      }
      return out;
    }
    centroidiBark() {
      const out = {};
      for (const [c, [f1, f2]] of Object.entries(this.centroidiHz())) out[c] = [bark(f1), bark(f2)];
      return out;
    }
    pronta() { const c = this.centroidiHz(); return ['é', 'è', 'ó', 'ò'].every((k) => c[k]); }
    avvisi() {
      const out = [], cb = this.centroidiBark();
      for (const [chiusa, aperta] of [['é', 'è'], ['ó', 'ò']]) {
        if (cb[chiusa] && cb[aperta]) {
          const d = dist(cb[chiusa], cb[aperta]), df1 = cb[aperta][0] - cb[chiusa][0];
          if (df1 < 0.3) out.push(`${chiusa}/${aperta}: nelle parole di controllo non c'è differenza di apertura (ΔF1 ${df1.toFixed(2)} Bark): ripeti la taratura con più attenzione`);
          else if (d < 0.5) out.push(`${chiusa}/${aperta}: differenza piccola (${d.toFixed(2)} Bark), giudizi meno sicuri`);
        }
      }
      for (const c of ['é', 'è', 'ó', 'ò']) {
        const n = (this.campioni[c] || []).length;
        if (n > 0 && n < 3) out.push(`${c}: solo ${n} campioni`);
      }
      return out;
    }
    classifica(m) {
      if (m.f1 == null || m.f2 == null) return m;
      const cb = this.centroidiBark();
      const cats = Object.keys(cb);
      if (!cats.length) return m;
      const z = [bark(m.f1), bark(m.f2)];
      m.piuVicina = cats.reduce((x, y) => (dist(z, cb[x]) <= dist(z, cb[y]) ? x : y));
      if (COPPIE_APERTURA[m.attesa]) {
        const [chiusa, aperta] = COPPIE_APERTURA[m.attesa];
        if (cb[chiusa] && cb[aperta]) {
          const c0 = cb[chiusa], c1 = cb[aperta];
          const ax = [c1[0] - c0[0], c1[1] - c0[1]], n2 = ax[0] ** 2 + ax[1] ** 2;
          if (n2 > 1e-6) {
            m.apertura = Math.round(((z[0] - c0[0]) * ax[0] + (z[1] - c0[1]) * ax[1]) / n2 * 100) / 100;
            m.giudizio = m.apertura < SOGLIA_CHIUSA ? 'chiusa' : m.apertura > SOGLIA_APERTA ? 'aperta' : 'intermedia';
            const voluta = (m.attesa === 'é' || m.attesa === 'ó') ? 'chiusa' : 'aperta';
            m.esito = m.giudizio === voluta ? 'ok' : (m.giudizio === 'intermedia' ? '~' : 'ERRORE');
          }
        }
      } else if (m.attesa) {
        m.esito = m.piuVicina === m.attesa ? 'ok' : 'da verificare';
      }
      return m;
    }
  }

  // ------------------------------------------------------------ doppie
  function eCoppiaDoppia(scempia, doppia) {
    const s = senzaAccenti(scempia.toLowerCase()), d = senzaAccenti(doppia.toLowerCase());
    if (d.length !== s.length + 1) return false;
    for (let i = 0; i < s.length; i++) {
      if (!VOCALI.has(s[i]) && s.slice(0, i + 1) + s[i] + s.slice(i + 1) === d) return true;
    }
    return false;
  }

  function confrontaDoppie(misure) {
    const out = [];
    for (let i = 0; i < misure.length - 1; i++) {
      const a = misure[i], b = misure[i + 1];
      if (eCoppiaDoppia(a.parola, b.parola) && a.consonanteMs && b.consonanteMs) {
        const r = b.consonanteMs / a.consonanteMs;
        out.push({ coppia: `${a.parola}/${b.parola}`, scempia: a.consonanteMs, doppia: b.consonanteMs,
          rapporto: Math.round(r * 100) / 100, vocale: [a.vocaleMs, b.vocaleMs],
          giudizio: r >= RAPPORTO_DOPPIA_OK ? 'distinta' : r >= RAPPORTO_DOPPIA_DEBOLE ? 'debole' : 'NON distinta' });
      }
    }
    return out;
  }

  const API = { VOCALI, CATEGORIE, PROFILI_VOCE, SOGLIA_CHIUSA, SOGLIA_APERTA, bark, senzaAccenti, analizzaTesto,
    ricampiona, livelli, calcolaTracce, burg, radici, formantiFrame, preparaFormanti, misuraFormanti, trovaSegmenti,
    assegnaAParole, trovaNuclei, confiniVocale, misuraParola, misuraSerie, misuraClip, Taratura, eCoppiaDoppia,
    confrontaDoppie };
  if (typeof module !== 'undefined' && module.exports) module.exports = API;
  else root.Dizione = API;
})(typeof self !== 'undefined' ? self : this);
