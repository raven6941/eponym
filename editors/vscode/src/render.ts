// Renders a boxToJson tree (eponym/shedLayout, issue #135) as nested
// HTML/CSS, Epigram deduction style: premises above a rule line, hole
// below. vscode-free: shared by the webview and the smoke test.

import { BoxJson } from "./protocol";

function esc(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

// Every hole in the tree gets a stable DOM id "hole-<id>".
export function boxToHtml(b: BoxJson): string {
  // Defensive: older servers may omit empty arrays — never crash on a
  // partial box.
  const holeIds = b.holeIds ?? [];
  const premises = b.premises ?? [];
  const children = b.children ?? [];
  const header = b.header ?? [];
  const holeGoal = b.holeGoal ?? "";
  const ruleLabel = b.ruleLabel ?? "";
  const isHole = holeIds.length > 0 && premises.length === 0 && children.length === 0;
  const cls = isHole ? "box hole" : "box";
  const holeAttr = isHole ? ` data-hole="${holeIds[0]}" data-goal="${esc(holeGoal)}"` : "";
  let inner = "";
  if (header.length > 0)
    inner += header.map((h) => `<div class="header">${esc(h)}</div>`).join("");
  if (premises.length > 0) {
    inner += `<div class="premises">` + premises.map(boxToHtml).join("") + `</div>`;
  }
  if (ruleLabel) inner += `<div class="rule"><span class="ruleline"></span><span class="rulelabel">${esc(ruleLabel)}</span></div>`;
  if (b.conclusion) inner += `<div class="conclusion">` + boxToHtml(b.conclusion) + `</div>`;
  if (children.length > 0) {
    inner += `<div class="children">` + children.map(boxToHtml).join("") + `</div>`;
  }
  if (!inner && isHole) inner = `<div class="holemark">?${holeIds[0]}</div>`;
  return `<div class="${cls}"${holeAttr}>${inner}</div>`;
}

export const css = `
body { font-family: monospace; background: #1e1e1e; color: #d4d4d4; padding: 16px; }
.box { border: 1px solid #555; border-radius: 4px; padding: 6px 10px; margin: 4px; display: inline-block; vertical-align: top; background: #252526; }
.hole { border: 2px dashed #d7ba7d; cursor: pointer; background: #2d2a1e; }
.hole:hover { background: #3a3524; }
.premises { display: flex; flex-direction: row; }
.children { display: flex; flex-direction: column; }
.rule { display: flex; align-items: center; margin: 2px 0; }
.ruleline { flex: 1; border-top: 2px solid #888; }
.rulelabel { margin-left: 6px; color: #9cdcfe; font-size: 0.85em; }
.header { color: #c586c0; }
#shedbar { position: sticky; top: 0; background: #0e0e0e; border: 1px solid #444; padding: 8px; margin-bottom: 12px; display: flex; gap: 8px; align-items: center; }
#goalpane { min-height: 2em; flex: 1; }
#refinebar { margin-top: 12px; }
button { margin-left: 6px; }
select { background: #252526; color: #d4d4d4; border: 1px solid #555; padding: 2px 6px; }
`;

// Issue #190: the webview carries a shed picker so the user can switch
// sheds in-view instead of closing the panel and re-running the command.
// `shedNames` lists every shed in the file's sidecar; the extension
// handles the `switch-shed` message by re-rendering with the new shed.
export function pageHtml(layoutJson: string, shedName: string, shedNames: string[] = []): string {
  // layoutJson is the raw JSON string of {"box": ...} — parsed in-page so
  // the extension only has to forward the string.
  const names = shedNames.length > 0 ? shedNames : [shedName];
  const options = names
    .map((n) => `<option value="${esc(n)}"${n === shedName ? " selected" : ""}>${esc(n)}</option>`)
    .join("");
  return `<!DOCTYPE html><html><head><meta charset="utf-8"><style>${css}</style></head><body>
<div id="shedbar"><label for="shedpicker">shed:</label><select id="shedpicker" onchange="switchShed(this.value)">${options}</select><span id="goalpane">Click a hole (?n) to see its goal.</span></div>
<div id="tree"></div>
<div id="refinebar">
  <input id="term" placeholder="refine term (e.g. zero())" size="40"/>
  <button onclick="refine()">refine</button>
  <button onclick="give()">give</button>
  <button onclick="casesplit()">case-split</button>
  <span id="actionmsg"></span>
</div>
<script>
const vscode = acquireVsCodeApi();
const layout = ${layoutJson};
let selectedHole = null;
function escHtml(s){ const d=document.createElement('div'); d.textContent=s; return d.innerHTML; }
function renderBox(b){
  const holeIds = b.holeIds || [];
  const premises = b.premises || [];
  const children = b.children || [];
  const header = b.header || [];
  const isHole = holeIds.length>0 && premises.length===0 && children.length===0;
  let inner="";
  if(header.length>0) inner+=header.map(h=>'<div class="header">'+escHtml(h)+'</div>').join('');
  if(premises.length>0) inner+='<div class="premises">'+premises.map(renderBox).join('')+'</div>';
  if(b.ruleLabel) inner+='<div class="rule"><span class="ruleline"></span><span class="rulelabel">'+escHtml(b.ruleLabel)+'</span></div>';
  if(b.conclusion) inner+='<div class="conclusion">'+renderBox(b.conclusion)+'</div>';
  if(children.length>0) inner+='<div class="children">'+children.map(renderBox).join('')+'</div>';
  if(!inner && isHole) inner='<div class="holemark">?'+holeIds[0]+'</div>';
  const attrs = isHole ? ' data-hole="'+holeIds[0]+'" data-goal="'+escHtml(b.holeGoal||'')+'"' : '';
  return '<div class="box'+(isHole?' hole':'')+'"'+attrs+'>'+inner+'</div>';
}
document.getElementById('tree').innerHTML = renderBox(layout.box);
document.querySelectorAll('.hole').forEach(el=>{
  el.addEventListener('click', ()=>{
    selectedHole = el.getAttribute('data-hole');
    document.getElementById('goalpane').textContent = '?'+selectedHole+' : '+el.getAttribute('data-goal');
  });
});
function refine(){ const t=document.getElementById('term').value; vscode.postMessage({cmd:'refine', term:t, hole:selectedHole}); }
function give(){ const t=document.getElementById('term').value; vscode.postMessage({cmd:'give', term:t, hole:selectedHole}); }
function casesplit(){ const v=document.getElementById('term').value; vscode.postMessage({cmd:'case-split', variable:v, hole:selectedHole}); }
function switchShed(name){ vscode.postMessage({cmd:'switch-shed', shedName:name}); }
window.addEventListener('message', e=>{
  const m=e.data;
  if(m.cmd==='actionmsg') document.getElementById('actionmsg').textContent=m.text;
  if(m.cmd==='rerender'){ location.reload(); }
});
</script></body></html>`;
}
