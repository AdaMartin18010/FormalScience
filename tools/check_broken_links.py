import json

with open('current_broken_links_v2.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

for k, v in data.items():
    t = type(v).__name__
    length = len(v) if hasattr(v, '__len__') else 'N/A'
    print(f'{k}: type={t}, len={length}')
    if isinstance(v, list) and v:
        print(f'  First item type: {type(v[0]).__name__}')
        if isinstance(v[0], dict):
            print(f'  First item keys: {list(v[0].keys())}')
            print(f'  Sample: {v[0]}')
    elif isinstance(v, dict) and v:
        first_k = list(v.keys())[0]
        print(f'  First key: {first_k}')
        print(f'  First val type: {type(v[first_k]).__name__}')
