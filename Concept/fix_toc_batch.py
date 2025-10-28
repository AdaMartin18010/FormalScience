import re
import sys

files_to_fix = [
    r'FormalLanguage_Perspective\09_26_Stages_Analysis\09.2_Future_26_Stages_Roadmap.md',
    r'FormalLanguage_Perspective\10_Consciousness_Machine_Integration\10.1_Human_Computer_Cognitive_Fusion.md',
]

for filepath in files_to_fix:
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        # Find both ## 目录 positions
        toc_positions = []
        for i, line in enumerate(lines):
            if re.match(r'^## 目录', line):
                toc_positions.append(i)
        
        if len(toc_positions) >= 2:
            # Delete from first --- before first TOC to --- before second TOC
            start = toc_positions[0] - 2  # Include the --- line
            end = toc_positions[1] - 2
            new_lines = lines[:start+1] + lines[end:]
            
            with open(filepath, 'w', encoding='utf-8') as f:
                f.writelines(new_lines)
            print(f'✓ Fixed: {filepath}')
        else:
            print(f'✗ Skipped (not 2 TOCs): {filepath}')
    except Exception as e:
        print(f'✗ Error in {filepath}: {e}')
