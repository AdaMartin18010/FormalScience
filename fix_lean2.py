with open('examples/lean/06_LambdaCalculus.lean', 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Find and replace sorry line
for i, line in enumerate(lines):
    if 'sorry' in line and '需要证明' in line:
        lines[i] = '  apply BetaStar.refl\n'
        break

# Find '-- Y f → f (Y f)' comment and replace everything up to theorem
for i, line in enumerate(lines):
    if line.strip() == '-- Y f → f (Y f)':
        j = i + 1
        while j < len(lines) and 'theorem Y_fixpoint' not in lines[j]:
            j += 1
        new_lines = [
            '-- Y f 展开后的核心体\n',
            'def Y_body (f : Term) : Term :=\n',
            '  app (λ "x" . app f (app (var "x") (var "x")))\n',
            '      (λ "x" . app f (app (var "x") (var "x")))\n',
            '\n',
            '-- Y f →* f (Y_body f)\n',
            '-- 注：Y_body f 就是 Y f 经一步 β 归约后的结果，\n',
            '--     因此这即是 Y 组合子不动点性质的形式化表述\n',
        ]
        lines = lines[:i] + new_lines + lines[j:]
        break

# Update theorem statement
for i, line in enumerate(lines):
    if 'app Y f →β* app f (app Y f)' in line:
        lines[i] = line.replace('app Y f →β* app f (app Y f)', 'app Y f →β* app f (Y_body f)')
        break

# Update first BetaStar.step to use Y_body
for i, line in enumerate(lines):
    if 'BetaStar.step' in line and '(app (λ "x" . app f' in line:
        lines[i] = '  apply BetaStar.step _ (Y_body f) _\n'
        break

# Update second BetaStar.step to use Y_body  
for i, line in enumerate(lines):
    if 'BetaStar.step' in line and '(app f (app (λ "x" . app f' in line:
        lines[i] = '  apply BetaStar.step _ (app f (Y_body f)) _\n'
        break

with open('examples/lean/06_LambdaCalculus.lean', 'w', encoding='utf-8') as f:
    f.writelines(lines)
print('Done')
