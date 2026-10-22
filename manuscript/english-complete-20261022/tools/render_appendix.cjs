const fs=require('fs');
const path=require('path');
const {pathToFileURL}=require('url');
const md=require('markdown-it')({html:true,breaks:false,linkify:false,typographer:false});
const katex=require('katex');
const puppeteer=require('puppeteer-core');
const root=path.resolve(__dirname,'..');
const out=root;
const basename=process.env.OUTPUT_BASENAME||'technical_appendix';
const input=process.env.INPUT_MD||basename+'.md';
fs.mkdirSync(path.join(out,'build'),{recursive:true});
let source=fs.readFileSync(path.join(out,input),'utf8');
source=source.replace('# English Technical Appendix','# English Technical Appendix\n\n<!-- CONTENTS -->');
const blocks=[],formulas=[],errors=[],substitutions=[];
source=source.replace(/```[^\n]*\n[\s\S]*?```/g,m=>{const i=blocks.push(m)-1;return `SIXCODETOKEN${i}END`;});
source=source.replace(/\\\[([\s\S]*?)\\\]|\$\$([\s\S]*?)\$\$|\\\(([\s\S]*?)\\\)|(?<!\\)\$([^$\n]+?)\$/g,(m,a,b,c,d,offset)=>{
 const display=a!==undefined||b!==undefined;
 let tex=(a??b??c??d).trim();
 // Typesetting-only correction: a Greek math command cannot occur inside \text.
 const i=formulas.length;
 // Unicode characters copied from the original proof are intentionally retained.
 let rendered;
 try {rendered=katex.renderToString(tex,{displayMode:display,throwOnError:true,strict:'ignore',output:'html',trust:false,macros:{'\\R':'\\mathbb{R}'}});}
 catch(e){errors.push({index:i,tex,error:e.message});rendered='<span class="math-error">'+md.utils.escapeHtml(tex)+'</span>';}
 formulas.push({display,tex,rendered});
 return `SIXMATHTOKEN${i}END`;
});
source=source.replace(/\\overline S/g,()=>{
 substitutions.push('Rendered a bare overline S command as inline mathematics.');
 const i=formulas.length,tex='\\overline S';
 formulas.push({display:false,tex,rendered:katex.renderToString(tex,{throwOnError:true,output:'html'})});
 return `SIXMATHTOKEN${i}END`;
});
source=source.replace(/SIXCODETOKEN(\d+)END/g,(_,i)=>blocks[+i]);
// Research notes sometimes close emphasis immediately before a Latin symbol.
// Make the paired markers explicit instead of leaving literal asterisks in print.
source=source.replace(/\*\*([^\n]+?)\*\*/g,'<strong>$1</strong>');
let html=md.render(source);
html=html.replace(/<p>SIXMATHTOKEN(\d+)END<\/p>/g,(_,i)=>`<div class="formula" data-math="${i}">${formulas[+i].rendered}</div>`);
html=html.replace(/SIXMATHTOKEN(\d+)END/g,(_,i)=>formulas[+i].display?`<div class="formula" data-math="${i}">${formulas[+i].rendered}</div>`:formulas[+i].rendered);

// Stable unique anchors for all headings and links for source-module references.
let hcount=0;const headings=[];
html=html.replace(/<h([1-6])>([\s\S]*?)<\/h\1>/g,(all,l,t)=>{
 const id='heading-'+(++hcount);const text=t.replace(/<[^>]+>/g,'');
 headings.push({id,level:+l,text});
 const moduleTitle=/^R\d+[A-Z]?\./.test(text);
 const firstModule=/^(R2|R9|R20|R24|R13|R29|R40|R49|R60)\./.test(text);
 return `<h${l} id="${id}"${moduleTitle?' class="module-title'+(firstModule?' first-module':'')+'"':''}>${t}</h${l}>`;
});
html=html.replace(/(?:<p>)?(<a id="[^"]+"><\/a>)(?:<\/p>)?\s*(<h[1-6][^>]*>)/g,'$2$1');
const tocFile=path.join(__dirname,'toc_pages.json');
const tocPages=fs.existsSync(tocFile)?JSON.parse(fs.readFileSync(tocFile,'utf8')):{};
const toc=headings.filter(x=>x.level===1 && x.text!=='English Technical Appendix').map(x=>`<li><a href="#${x.id}">${x.text}<span class="toc-page">${tocPages[x.text]??''}</span></a></li>`).join('');
html=html.replace('<!-- CONTENTS -->',`<nav class="toc"><h2>Contents</h2><ol>${toc}</ol><p>Stable R identifiers match the evidence. PDF bookmarks expand to modules and sections.</p></nav>`);
const katexRoot=path.dirname(require.resolve('katex/package.json'));
let css=fs.readFileSync(path.join(katexRoot,'dist/katex.min.css'),'utf8');
css=css.replace(/url\((fonts\/[^)]+)\)/g,(_,p)=>{const buff=fs.readFileSync(path.join(katexRoot,'dist',p));const ext=path.extname(p).slice(1);return `url(data:font/${ext};base64,${buff.toString('base64')})`;});
const style=`
@page {size:A4; margin:19mm 19mm 19mm 19mm;}
* {box-sizing:border-box;}
body{font-family:"Times New Roman",Georgia,serif;font-size:10.5pt;line-height:1.48;color:#171717;margin:0;}
main{width:172mm;margin:0 auto;}
h1,h2,h3,h4,h5{font-family:Georgia,serif;line-height:1.45;break-after:avoid;page-break-after:avoid;}
h1{font-size:20pt;margin:0 0 7mm;break-before:page;padding-top:2mm;border-bottom:1px solid #a6afb5;padding-bottom:3mm;}
h1:first-child{break-before:auto;font-size:28pt;margin-top:15mm;}
h2{font-size:15pt;margin-top:9mm;margin-bottom:4mm;}
.module-title{break-before:page;}
.module-title.first-module{break-before:auto;}
h3{font-size:12pt;margin-top:6mm;margin-bottom:3mm;}
h4,h5{font-size:11pt;margin-top:4mm;margin-bottom:2mm;}
p{margin:2.6mm 0;orphans:3;widows:3;text-align:justify;overflow-wrap:anywhere;}
p:has(code){text-align:left;}
.math-punctuation{white-space:nowrap;}
a{color:#164d6c;text-decoration:none;}
strong{font-weight:700;}
li{margin:1.8mm 0;}
ul,ol{padding-left:7mm;}
code{font-family:Consolas,monospace;font-size:8.8pt;overflow-wrap:anywhere;word-break:break-all;}
pre{white-space:pre-wrap;border:1px solid #d5dce0;background:#f6f8f9;padding:3mm;line-height:1.5;break-inside:avoid;}
pre code{word-break:normal;}
.module-note{font-family:Georgia,serif;font-size:9pt;line-height:1.48;background:#f1f5f7;border-left:2pt solid #667e8b;padding:3mm 4mm;margin:3mm 0 5mm;overflow-wrap:anywhere;break-inside:avoid;}
.formula{margin:3mm 0;break-inside:avoid;page-break-inside:avoid;}
.katex{font-size:1.08em;line-height:1.2;}
.katex-display{margin:0;}
.katex-display>.katex{white-space:nowrap;display:block;}
.katex-display>.katex>.katex-html{white-space:nowrap;display:block;position:relative;}
.katex-display .tag{right:0;}
.page-break{display:none;}
.toc{font-family:Georgia,serif;font-size:10pt;}
.toc{break-before:page;}
.toc h2{margin-top:0;}
.toc ol{columns:2;column-gap:8mm;list-style:none;padding:0;}
.toc li{break-inside:avoid;margin:0 0 2.5mm;}
.toc li a{display:grid;grid-template-columns:minmax(0,1fr) 25px;gap:4px;align-items:start;}
.toc-page{float:none;text-align:right;white-space:nowrap;font-variant-numeric:tabular-nums;}
blockquote{margin:3mm 0;padding:0 4mm;border-left:2px solid #adb6bc;color:#444;}
table{border-collapse:collapse;font-size:9pt;width:100%;margin:4mm 0;}
th,td{border:1px solid #aaa;padding:1.5mm;}
tr{break-inside:avoid;}
@media screen {body{background:#e9ecee;padding:12mm 0;}main{background:white;padding:18mm;width:210mm;box-shadow:0 2px 16px #bbc;}}
@media print{a{color:inherit;}h2:has(+ .module-note){break-before:page;}h1+h2{break-before:auto!important;}nav{break-inside:avoid;}}
`;
let document=`<!DOCTYPE html><html lang="en"><head><meta charset="UTF-8"><title>Six unit squares: English technical appendix</title><style>${css}\n${style}</style></head><body><main>${html}</main></body></html>`;
fs.writeFileSync(path.join(out,basename+'.html'),document);
fs.writeFileSync(path.join(out,basename+'_math_render_report.json'),JSON.stringify({formulas:formulas.length,display:formulas.filter(x=>x.display).length,errors,typesetting_substitutions:substitutions,source_to_english_formula_identity_claimed:false},null,2));
fs.writeFileSync(path.join(out,basename+'_heading_index.json'),JSON.stringify(headings,null,2));
if(errors.length){console.log(JSON.stringify({formulas:formulas.length,errors:errors.length,examples:errors.slice(0,15)},null,2));process.exit(2);}

(async()=>{
 const browser=await puppeteer.launch({executablePath:process.env.CHROME_PATH||'C:/Program Files/Google/Chrome/Application/chrome.exe',headless:true,args:['--allow-file-access-from-files','--disable-gpu'],timeout:60000});
 const page=await browser.newPage();
 await page.setViewport({width:900,height:1000});
 await page.emulateMediaType('print');
 await page.goto(pathToFileURL(path.join(out,basename+'.html')).href,{waitUntil:'load',timeout:120000});
 await page.evaluate(()=>document.fonts.ready);
 const layout=await page.evaluate(()=>{
  let scaled=[];let over=[];
  for(const el of document.querySelectorAll('.formula')){
   const k=el.querySelector('.katex');if(!k)continue;
   const avail=el.getBoundingClientRect().width;
   const span=k.querySelector('.katex-html');
   const base=Array.from(span.children).filter(x=>!x.classList.contains('tag'));
   const w=base.reduce((n,x)=>n+x.getBoundingClientRect().width,0);
   const tag=span.querySelector('.tag');const tagw=tag?tag.getBoundingClientRect().width+12:0;
   if(w+tagw>avail){
    const old=parseFloat(getComputedStyle(k).fontSize),factor=(avail-tagw)/w*.98;
    k.style.fontSize=(old*factor)+'px';
    scaled.push({index:+el.dataset.math,factor,pt:old*factor*.75,width:w,available:avail});
   }
  }
  for(const a of document.querySelectorAll('a[href^="#"]')) if(!document.getElementById(a.getAttribute('href').slice(1))) over.push(a.outerHTML);
  return {scaled,brokenInternalLinks:over};
 });
 // Save size corrections into the portable offline HTML too.
 document=await page.content();fs.writeFileSync(path.join(out,basename+'.html'),document);
 fs.writeFileSync(path.join(out,basename+'_layout_report.json'),JSON.stringify(layout,null,2));
 await page.pdf({path:path.join(out,'build',basename+'.pdf'),format:'A4',printBackground:true,preferCSSPageSize:true,displayHeaderFooter:true,headerTemplate:'<div style="font-size:8px;width:100%;text-align:center;color:#666;">S(6)=2 | English technical appendix | candidate argument</div>',footerTemplate:'<div style="font-size:9px;width:100%;text-align:center;color:#555;">A-<span class="pageNumber"></span> / <span class="totalPages"></span></div>',outline:true,tagged:true,timeout:180000});
 await browser.close();
 console.log(JSON.stringify({formulas:formulas.length,scaled:layout.scaled.length,minPt:Math.min(...layout.scaled.map(x=>x.pt)),brokenLinks:layout.brokenInternalLinks.length}));
})().catch(e=>{console.error(e);process.exit(1);});
