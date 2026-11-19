# Dizione

Pagina-app per esercitarsi nella dizione italiana dal telefono: misura l'apertura
delle vocali (é/è, ó/ò) e la durata delle consonanti doppie, con una taratura sulla
propria voce. L'analisi acustica (formanti con LPC di Burg, come Praat) avviene
interamente nel browser: le registrazioni non lasciano il telefono.

- `index.html` — interfaccia (taratura, test, esercizi, storico, esportazione CSV)
- `dsp.js` — motore di analisi, porting del server MCP "dizione" usato sul PC
- `sw.js`, `manifest.webmanifest`, icone — uso offline e installazione sulla schermata Home
