# regla295_md2html.py (1 Oct 2026): copy of regla293_md2html.py; a long cell (more than 40 characters) in one of the first two
# columns of a table may wrap (class "w"), tables are at most as wide as the text, and a table of more than 12 rows may break
# across pages (class "long"). File paths and identifiers with underscores are printed as code, not as mathematics. In the earlier builder such cells never
# wrapped, and the notation table of section 1.9 and the table of the supplementary note overflowed the page in the PDF.
# regla293_md2html.py (1 Oct 2026): copy of regla277_md2html.py with an optional title in argv[3].
# regla277_md2html.py — copy of regla272_md2html.py with footnotes, for PAPER_OFICIAL_v4 (Grepy el Auditor, 2026-09-25).
# Footnotes: inline [^n] -> superscript; a line '[^n]: text' -> a small note printed right after the paragraph.
# No external packages. Handles: headings, paragraphs, bold/italic, inline code (rendered as math, with
# ^{..}/_{..} turned into sup/sub), display formulas (a line that is only code), nested lists, blockquotes,
# tables, horizontal rules. Usage: python3 regla272_md2html.py IN.md OUT.html
import sys, re, html

def mathify(s):
    # s: raw code-span content (unescaped). Convert ^{..}, _{..}, ^c, _c into sup/sub, recursively.
    out = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c in '^_' and i + 1 < n and i > 0:
            tag = 'sup' if c == '^' else 'sub'
            if s[i+1] == '{':
                depth, j = 0, i + 1
                while j < n:
                    if s[j] == '{': depth += 1
                    elif s[j] == '}':
                        depth -= 1
                        if depth == 0: break
                    j += 1
                inner = s[i+2:j]
                out.append(f'<{tag}>{mathify(inner)}</{tag}>')
                i = j + 1
                continue
            else:
                ch = s[i+1]
                # keep combining marks with their base character
                k = i + 2
                while k < n and 0x0300 <= ord(s[k]) <= 0x036F: k += 1
                out.append(f'<{tag}>' + html.escape(s[i+1:k]).replace('*', '&#42;') + f'</{tag}>')
                i = k
                continue
        out.append(html.escape(c).replace('*', '&#42;'))
        i += 1
    return ''.join(out)

def code_html(content):
    if (re.search(r'\.(py|log|md|txt|cpp|m2|pdf|lean|json|sage|html)\b', content)
            or (re.fullmatch(r'[A-Za-z0-9_.\-]+(/[A-Za-z0-9_.\-]+)*/?', content) and '/' in content and re.search(r'[A-Za-z]{3,}', content))
            or re.fullmatch(r'[A-Za-z]{2,}[A-Za-z0-9]*(_[A-Za-z][A-Za-z0-9]+)+', content)):
        return '<code class="file">' + html.escape(content).replace('*', '&#42;') + '</code>'
    return f'<span class="m">{mathify(content)}</span>'

def inline(s):
    parts = re.split(r'(`[^`]*`)', s)
    res = []
    for p in parts:
        if p.startswith('`') and p.endswith('`') and len(p) >= 2:
            res.append(code_html(p[1:-1]))
        else:
            t = html.escape(p, quote=False)
            t = re.sub(r'\[\^(\w+)\]', r'<sup class="fnref">\1</sup>', t)
            t = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', t)
            t = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'<em>\1</em>', t)
            res.append(t)
    out = ''.join(res)
    # bold/italic spanning code spans: second pass on the assembled string outside tags is risky; handle **..** across spans
    out = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', out)
    out = re.sub(r'(?<![\w*>])\*(?!\s)([^*]+?)(?<!\s)\*(?![\w*])', r'<em>\1</em>', out)
    return out

def is_display(line):
    s = line.strip()
    if not s.startswith('`'): return False
    rest = re.sub(r'`[^`]*`', '', s)
    return (re.fullmatch(r'[\s,.;:()0-9]*', rest) is not None or re.fullmatch(r'[\s,.;:]*\([^()]*\)[\s.∎]*', rest) is not None) and s.count('`') >= 2

def split_row(line):
    line = line.strip()
    if line.startswith('|'): line = line[1:]
    if line.endswith('|'): line = line[:-1]
    cells, cur, incode = [], '', False
    for ch in line:
        if ch == '`': incode = not incode
        if ch == '|' and not incode:
            cells.append(cur); cur = ''
        else:
            cur += ch
    cells.append(cur)
    return [c.strip() for c in cells]

def convert(md):
    lines = md.split('\n')
    out = []
    i = 0
    first_h1 = True
    after_h1 = False
    para = []
    front = [True]
    def flush_para():
        nonlocal para
        if para:
            cls = ' class="front"' if front[0] else ''
            out.append(f'<p{cls}>' + ' '.join(inline(x) for x in para) + '</p>')
            para = []
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        if not s:
            flush_para(); i += 1; continue
        fm = re.match(r'^\[\^(\w+)\]:\s*(.*)$', s)
        if fm:
            flush_para()
            out.append(f'<div class="fn"><sup>{fm.group(1)}</sup>&#8201;' + inline(fm.group(2)) + '</div>')
            i += 1; continue
        if s == '---':
            flush_para(); out.append('<hr/>'); front[0] = False; i += 1; continue
        m = re.match(r'^(#{1,4})\s+(.*)$', s)
        if m:
            flush_para()
            lvl = len(m.group(1)); txt = inline(m.group(2))
            if lvl == 1 and first_h1:
                out.append(f'<h1 class="title">{txt}</h1>'); first_h1 = False; after_h1 = True
            elif lvl == 2 and after_h1:
                out.append(f'<h2 class="subtitle">{txt}</h2>'); after_h1 = False
            else:
                out.append(f'<h{lvl}>{txt}</h{lvl}>'); after_h1 = False
            i += 1; continue
        after_h1 = False
        if s.startswith('|') and i + 1 < len(lines) and re.match(r'^\|?\s*:?-{3,}', lines[i+1].strip()):
            flush_para()
            head = split_row(s); i += 2
            rows = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                rows.append(split_row(lines[i])); i += 1
            def cell(tag, c):
                long = len(re.sub(r'[`*]', '', c)) > 40
                return f'<{tag} class="w">{inline(c)}</{tag}>' if long else f'<{tag}>{inline(c)}</{tag}>'
            h = ('<table class="long">' if len(rows) > 12 else '<table>') + '<thead><tr>' + ''.join(cell('th', c) for c in head) + '</tr></thead><tbody>'
            for r in rows:
                h += '<tr>' + ''.join(cell('td', c) for c in r) + '</tr>'
            out.append(h + '</tbody></table>')
            continue
        if s.startswith('>'):
            flush_para()
            buf = []
            while i < len(lines) and lines[i].strip().startswith('>'):
                buf.append(lines[i].strip()[1:].strip()); i += 1
            parts, cur, items = [], [], []
            for x in buf:
                if x.startswith('- '):
                    if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
                    items.append(inline(x[2:]))
                else:
                    if items: parts.append('<ul>' + ''.join(f'<li>{t}</li>' for t in items) + '</ul>'); items = []
                    if x and is_display(x):
                        if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
                        parts.append('<div class="display">' + inline(x) + '</div>')
                    elif x: cur.append(x)
                    elif cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
            if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>')
            if items: parts.append('<ul>' + ''.join(f'<li>{t}</li>' for t in items) + '</ul>')
            out.append('<blockquote>' + ''.join(parts) + '</blockquote>')
            continue
        lm = re.match(r'^(\s*)([-*]|\d+\.)\s+(.*)$', line)
        if lm:
            flush_para()
            # collect list block
            items = []  # (indent, ordered, text)
            while i < len(lines):
                l = lines[i]
                mm = re.match(r'^(\s*)([-*]|\d+\.)\s+(.*)$', l)
                if mm:
                    items.append([len(mm.group(1)), mm.group(2)[0].isdigit(), mm.group(3)]); i += 1
                elif l.strip() and l.startswith(' ') and items:
                    items[-1][2] += ' ' + l.strip(); i += 1
                else:
                    break
            out.append(render_list(items))
            continue
        if is_display(line):
            flush_para()
            out.append('<div class="display">' + inline(s) + '</div>')
            i += 1; continue
        para.append(s); i += 1
    flush_para()
    return '\n'.join(out)

def render_list(items):
    html_out = []
    stack = []  # (indent, tag)
    for ind, ordered, text in items:
        tag = 'ol' if ordered else 'ul'
        while stack and ind < stack[-1][0]:
            html_out.append(f'</li></{stack[-1][1]}>'); stack.pop()
        if not stack or ind > stack[-1][0]:
            html_out.append(f'<{tag}>'); stack.append((ind, tag))
        else:
            html_out.append('</li>')
        html_out.append('<li>' + inline(text))
    while stack:
        html_out.append(f'</li></{stack[-1][1]}>'); stack.pop()
    return ''.join(html_out)

CSS = r'''
@page { size: A4; margin: 20mm 19mm 20mm 19mm; }
html { -webkit-print-color-adjust: exact; }
body { font-family: "STIX Two Text", "STIXGeneral", "Times New Roman", serif; font-size: 10.6pt; line-height: 1.46;
       color: #111; max-width: 172mm; margin: 0 auto; text-align: justify; hyphens: auto; }
h1.title { font-size: 25pt; text-align: center; letter-spacing: 0.06em; margin: 4mm 0 2mm 0; font-weight: 700; }
h2.subtitle { font-size: 13.5pt; text-align: center; font-weight: 400; font-style: italic; margin: 0 0 6mm 0; border: none; }
h2 { font-size: 14pt; margin: 7mm 0 2.5mm 0; padding-bottom: 1mm; border-bottom: 0.4pt solid #888; page-break-after: avoid; }
h3 { font-size: 11.6pt; margin: 4.5mm 0 1.5mm 0; page-break-after: avoid; }
h4 { font-size: 10.8pt; margin: 3mm 0 1mm 0; }
p { margin: 1.6mm 0; }
p.front { text-align: center; margin: 1.2mm 6mm; }
.m { font-family: "STIX Two Text", "STIX Two Math", "STIXGeneral", serif; font-style: italic; white-space: normal; }
em .m, blockquote em .m { font-style: normal; }
.m sub, .m sup { font-size: 72%; line-height: 0; }
code.file { font-family: "Menlo", monospace; font-size: 8.6pt; color: #333; }
.display { text-align: center; margin: 2.2mm 0; }
blockquote { margin: 3mm 4mm; padding: 2.5mm 4mm; border-left: 2.5pt solid #444; background: #f4f4f4; }
blockquote p { margin: 1mm 0; }
blockquote ul { margin: 0.8mm 0 0.8mm 2mm; }
.display .m { font-style: italic; }
ul, ol { margin: 1.2mm 0 1.2mm 6mm; padding-left: 4mm; }
li { margin: 0.6mm 0; }
table { border-collapse: collapse; margin: 3mm auto; font-size: 9.2pt; page-break-inside: avoid; }
th, td { border: 0.4pt solid #999; padding: 1.2mm 2mm; text-align: center; vertical-align: top; }
th { background: #eee; }
td:nth-child(-n+2), th:nth-child(-n+2) { white-space: nowrap; }
td.w, th.w { white-space: normal !important; }
table { max-width: 100%; }
table.long { page-break-inside: auto; }
tr { page-break-inside: avoid; }
thead { display: table-header-group; }
hr { border: none; border-top: 0.4pt solid #aaa; margin: 5mm 0; }
strong { font-weight: 700; }
sup.fnref { font-size: 70%; line-height: 0; }
.fn { font-size: 8.4pt; line-height: 1.35; margin: 1.4mm 0 2.4mm 0; text-align: justify; color: #222; }
.fn::before { content: ""; display: block; width: 32%; border-top: 0.4pt solid #999; margin-bottom: 0.9mm; }
.fn sup { font-size: 75%; }
'''

if __name__ == '__main__':
    md = open(sys.argv[1], encoding='utf-8').read()
    body = convert(md)
    doc = ('<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><title>' + html.escape(sys.argv[3] if len(sys.argv) > 3 else 'The Chaise Longue Theorem') + '</title>'
           f'<style>{CSS}</style></head><body>\n{body}\n</body></html>')
    open(sys.argv[2], 'w', encoding='utf-8').write(doc)
    print('ok', len(doc))
