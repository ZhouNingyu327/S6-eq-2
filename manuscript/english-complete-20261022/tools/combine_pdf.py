from pathlib import Path
import json,re,hashlib
from pypdf import PdfReader,PdfWriter
import logging
logging.getLogger("pypdf").setLevel(logging.ERROR)
import logging
logging.getLogger('pypdf').setLevel(logging.ERROR)
from pypdf.generic import NameObject,ArrayObject
ROOT=Path(__file__).resolve().parents[1]
P=ROOT;FULL=ROOT
core=PdfReader(FULL/'build/main.pdf');appendix=PdfReader(P/'build/technical_appendix.pdf')
def resolve_named_links(reader):
    destinations=reader.named_destinations;count=0;converted=0
    for page in reader.pages:
        for ref in page.get('/Annots',[]):
            annotation=ref.get_object()
            if annotation.get('/Subtype')!='/Link':continue
            count+=1
            owner=annotation;key='/Dest'
            if '/A'in annotation:
                action=annotation['/A']
                if action.get('/S')!='/GoTo':continue
                owner=action;key='/D'
            if key not in owner:continue
            value=owner[key]
            if isinstance(value,str):
                assert str(value)in destinations,('unresolved source destination',str(value))
                owner[NameObject(key)]=ArrayObject(destinations[str(value)].dest_array);converted+=1
    return count,converted
core_links,core_converted=resolve_named_links(core)
appendix_links,appendix_converted=resolve_named_links(appendix)
render=json.loads((P/'technical_appendix_math_render_report.json').read_text(encoding='utf-8'))
layout=json.loads((P/'technical_appendix_layout_report.json').read_text(encoding='utf-8'))
assert not render['errors']and not layout['brokenInternalLinks']
assert all(x['pt']>=8.5 for x in layout['scaled'])
modules=json.loads((P/'technical_appendix_assembly.json').read_text(encoding='utf-8'));assert modules['module_count']==72 and not modules['missing']
log=(FULL/'build/main.log').read_text(encoding='utf-8',errors='replace')
assert not re.search(r'Overfull|undefined references|Citation .+ undefined|Reference .+ undefined|multiply defined',log)
writer=PdfWriter();writer.append(core,outline_item='Core argument and geometric figures');writer.append(appendix,outline_item='Detailed English proofs: 72 modules')
writer.set_page_label(0,len(core.pages)-1,style='/D',start=1)
writer.set_page_label(len(core.pages),len(core.pages)+len(appendix.pages)-1,style='/D',prefix='A-',start=1)
writer.add_metadata({'/Title':'Six unit squares: complete English candidate manuscript','/Author':'Ningyu Zhou','/Subject':'Candidate argument for S(6)=2; English review edition 1.0, 22 October 2026','/Keywords':'unit square covering, geometric proof, computer-assisted candidate, exact certificates'})
out=ROOT/'S6_Complete_English_Candidate_20261022.pdf';out.parent.mkdir(parents=True,exist_ok=True)
with out.open('wb')as f:writer.write(f)
reader=PdfReader(out);texts=[p.extract_text()for p in reader.pages]
output_links=sum(1 for p in reader.pages for a in p.get('/Annots',[])if a.get_object().get('/Subtype')=='/Link')
assert output_links==core_links+appendix_links,('link annotations dropped',output_links,core_links+appendix_links)
assert not any(re.search('[\u3400-\u9fff]',t)for t in texts)
assert not any('INTERNAL PARTIAL PREVIEW'in t for t in texts)
assert not any(re.search(r'MATH\d{3,}|ZZZP\d|SIXMATHTOKEN',t)for t in texts)
locations={}
def walk(items):
    for item in items:
        if isinstance(item,list):walk(item);continue
        title=str(item.get('/Title',''))
        m=re.match(r'^(R\d+[A-Z]?)\.',title)
        if m:locations[m.group(1)]={'page':reader.get_destination_page_number(item)+1,'title':title}
walk(reader.outline)
assert set(locations)=={x['module']for x in modules['modules']},('missing module bookmarks',set(x['module']for x in modules['modules'])-set(locations))
info={'pdf':out.name,'pages':len(reader.pages),'core_pages':len(core.pages),'technical_pages':len(appendix.pages),'modules':72,'formulas_rendered':render['formulas'],'formula_parse_errors':0,'broken_internal_links':0,'link_annotations_preserved':output_links,'named_link_destinations_resolved_before_merge':core_converted+appendix_converted,'minimum_scaled_math_pt':min(x['pt']for x in layout['scaled']),'cjk_characters':0,'all_72_module_bookmarks_present':True,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'module_locations':locations,'mathematical_validity_checked':False}
(FULL/'pdf_assembly.json').write_text(json.dumps(info,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in info.items()if k!='module_locations'},indent=2))
