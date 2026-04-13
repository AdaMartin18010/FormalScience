import json
from collections import Counter

with open('current_broken_links_v2.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

fnf = data.get('file_not_found', [])

# Filter matter files
matter_items = [item for item in fnf if item['file'].startswith('.\\docs\\Matter\\')]
print(f'Total broken links in docs/Matter: {len(matter_items)}')

# Top matter files
src_counter = Counter(item['file'] for item in matter_items)
print('\nTop 10 docs/Matter files with broken links:')
for src, count in src_counter.most_common(10):
    print(f'  {count:>4}: {src}')

# Top missing targets in matter
target_counter = Counter(item['url'] for item in matter_items)
print('\nTop 10 missing targets in docs/Matter broken links:')
for target, count in target_counter.most_common(10):
    print(f'  {count:>4}: {target}')
