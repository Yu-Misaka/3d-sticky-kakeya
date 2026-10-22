"""Inline the prototype data and the proposal into one HTML page, published at /preview/."""
import json, re, sys
from pathlib import Path
from markdown_it import MarkdownIt

HERE = Path(__file__).resolve().parent
BLUEPRINT = HERE.parent
NOTES = BLUEPRINT / 'notes/frontend-redesign-plan.md'
DATA = BLUEPRINT / 'build/redesign/data'
out = Path(sys.argv[1]) if len(sys.argv) > 1 else BLUEPRINT / 'site-src/preview/index.html'


def script_json(path):
    return json.dumps(json.loads(path.read_text()), ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')


md = MarkdownIt('commonmark').enable('table')
notes = md.render(NOTES.read_text())
notes = notes.replace('<table>', '<div class="tw"><table>').replace('</table>', '</table></div>')
import base64
shots = [('desktop-load', '桌面打开时：图从 y = 633 开始'), ('desktop-panel', '桌面选中节点后：图剩 43% 宽，边改成绿和蓝'),
         ('phone-panel', '手机打开 #node-W2T5_2：抽屉上方是节点索引，看不到图')]
figure = '<div class="shots">' + ''.join(
    f'<figure><img alt="{cap}" src="data:image/webp;base64,{base64.b64encode((HERE / "before" / (name + ".webp")).read_bytes()).decode()}"><figcaption>{cap}</figcaption></figure>'
    for name, cap in shots) + '</div>'
notes = notes.replace('</table></div>', '</table></div>' + figure, 1)
page = (HERE / 'app.html').read_text()
for key, value in {'ATLAS': script_json(DATA / 'atlas.json'), 'LAYOUTS': script_json(DATA / 'layouts.json'),
                   'CHAPTER': script_json(DATA / 'chapter.json'), 'NOTES': notes}.items():
    page = page.replace('{{' + key + '}}', value)
# The Artifact host wraps the page in its own document; a local copy needs one too,
# or the browser falls back to quirks mode.
artifact = BLUEPRINT / 'build/redesign/preview.artifact.html'
artifact.write_text(page)
out.write_text('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
               '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">\n'
               + page + '\n</html>\n')
for path in (out, artifact):
    print(path, f'{path.stat().st_size / 1e6:.2f} MB')
