from pathlib import Path
import json
root=Path(__file__).resolve().parents[1]
parts=json.loads((root/'edition_structure.json').read_text(encoding='utf-8'))
out=[(root/'technical_preamble.md').read_text(encoding='utf-8')]
for p in parts:
    out.append('<a id="technical-part-'+p['part']+'"></a>\n# Technical Part '+p['part']+'. '+p['title']+'\n\n')
    out.append('Modules: '+', '.join('['+k+'](#'+k+')'for k in p['modules'])+'.\n\n')
    for k in p['modules']:out.append((root/'technical_modules'/(k+'.md')).read_text(encoding='utf-8').strip()+'\n\n')
out.append((root/'technical_index.md').read_text(encoding='utf-8'))
(root/'technical_appendix.md').write_text(''.join(out),encoding='utf-8',newline='\n')
print('Assembled',sum(len(p['modules'])for p in parts),'English modules.')
