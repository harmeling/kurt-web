#!/usr/bin/env python3
"""Generate browser highlighting metadata from kurt-lang's keywords dictionary."""
import ast, json
from pathlib import Path

web = Path(__file__).resolve().parents[1]
lang = Path(__import__('sys').argv[1] if len(__import__('sys').argv) > 1 else web.parent / 'kurt-lang')
source = lang / 'src/kurt/kurt.py'
tree = ast.parse(source.read_text(encoding='utf-8'))
keywords = None
version = None
for node in tree.body:
    if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == 'keywords':
        keywords = [key.value for key in node.value.keys]
    if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'version' for t in node.targets):
        version = node.value.value
if not keywords: raise SystemExit(f'keywords not found in {source}')
declarations = ['var','const','infix','postfix','prefix','brackets','arity','bindop','chain','flat','sym','bool','calc','alias']
payload = {
    'kurtVersion': version,
    'declarations': declarations,
    'commands': [word for word in keywords if word not in declarations],
    'helpers': ['with'],
    'constants': ['true','false'],
}
(web / 'language.json').write_text(json.dumps(payload, indent=2) + '\n', encoding='utf-8')
print(f'wrote language.json ({len(keywords)} commands for Kurt {version})')
