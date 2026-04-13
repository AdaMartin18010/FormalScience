import json
from collections import Counter, defaultdict

with open('current_broken_links_v2.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

file_not_found = data.get('file_not_found', [])
directory_links = data.get('directory_links', [])

print(f'file_not_found: {len(file_not_found)}')
print(f'directory_links: {len(directory_links)}')

# Top source files with broken links
src_counter = Counter(item['file'] for item in file_not_found)
print('\nTop 20 files with most broken links:')
for src, count in src_counter.most_common(20):
    print(f'  {count:>4}: {src}')

# Top missing targets
target_counter = Counter(item['url'] for item in file_not_found)
print('\nTop 20 missing targets:')
for target, count in target_counter.most_common(20):
    print(f'  {count:>4}: {target}')

# Categorize by source prefix
prefix_counter = Counter()
for item in file_not_found:
    src = item['file']
    if src.startswith('.\\docs\\Refactor\\'):
        prefix_counter['docs/Refactor'] += 1
    elif src.startswith('.\\Composed\\'):
        prefix_counter['Composed'] += 1
    elif src.startswith('.\\Concept\\'):
        prefix_counter['Concept'] += 1
    elif src.startswith('.\\FormalRE\\'):
        prefix_counter['FormalRE'] += 1
    elif src.startswith('.\\view\\'):
        prefix_counter['view'] += 1
    else:
        prefix_counter['other'] += 1

print('\nBy source prefix:')
for prefix, count in prefix_counter.most_common():
    print(f'  {count:>4}: {prefix}')
