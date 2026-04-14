with open('examples/lean/06_LambdaCalculus.lean', 'r', encoding='utf-8') as f:
    content = f.read()

# Find the broken theorem and replace it
start = content.find('theorem Y_fixpoint (f : Term) :')
end = content.find('end LambdaCalculus')

new_theorem = '''theorem Y_fixpoint (f : Term) : app Y f →β* app f (Y_body f) := by
  apply BetaStar.step _ (Y_body f) _
    (Beta1.beta "f" (app (λ "x" . app (var "f") (app (var "x") (var "x"))) 
      (λ "x" . app (var "f") (app (var "x") (var "x")))) f)
  apply BetaStar.step _ (app f (Y_body f)) _
    (Beta1.beta "x" (app f (app (var "x") (var "x"))) 
      (λ "x" . app f (app (var "x") (var "x"))))
  apply BetaStar.refl

'''

if start != -1 and end != -1:
    content = content[:start] + new_theorem + content[end:]
    with open('examples/lean/06_LambdaCalculus.lean', 'w', encoding='utf-8') as f:
        f.write(content)
    print('Fixed successfully')
else:
    print(f'start={start}, end={end}')
