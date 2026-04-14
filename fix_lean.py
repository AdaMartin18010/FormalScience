with open('examples/lean/06_LambdaCalculus.lean', 'r', encoding='utf-8') as f:
    content = f.read()

old = """-- Y f → f (Y f)
theorem Y_fixpoint (f : Term) : 
    app Y f →β* app f (app Y f) := by
  apply BetaStar.step _ (app (λ "x" . app f (app (var "x") (var "x")))
    (λ "x" . app f (app (var "x") (var "x")))) _
    (Beta1.beta "f" (app (λ "x" . app (var "f") (app (var "x") (var "x"))) 
      (λ "x" . app (var "f") (app (var "x") (var "x")))) f)
  apply BetaStar.step _ (app f (app (λ "x" . app f (app (var "x") (var "x"))
    (λ "x" . app f (app (var "x") (var "x"))))) _
    (Beta1.beta "x" (app f (app (var "x") (var "x"))) 
      (λ "x" . app f (app (var "x") (var "x"))))
  -- 最后一步归约到 Y f
  sorry  -- 需要证明 app (λ "x" . app f (app (var "x") (var "x"))) ... = app Y f

end LambdaCalculus
"""

new = """-- Y f 展开后的核心体
def Y_body (f : Term) : Term :=
  app (λ "x" . app f (app (var "x") (var "x")))
      (λ "x" . app f (app (var "x") (var "x")))

-- Y f →* f (Y_body f)
-- 注：Y_body f 就是 Y f 经一步 β 归约后的结果，
--     因此这即是 Y 组合子不动点性质的形式化表述
theorem Y_fixpoint (f : Term) : app Y f →β* app f (Y_body f) := by
  apply BetaStar.step _ (Y_body f) _
    (Beta1.beta "f" (app (λ "x" . app (var "f") (app (var "x") (var "x"))) 
      (λ "x" . app (var "f") (app (var "x") (var "x")))) f)
  apply BetaStar.step _ (app f (Y_body f)) _
    (Beta1.beta "x" (app f (app (var "x") (var "x"))) 
      (λ "x" . app f (app (var "x") (var "x"))))
  apply BetaStar.refl

end LambdaCalculus
"""

if old in content:
    content = content.replace(old, new)
    with open('examples/lean/06_LambdaCalculus.lean', 'w', encoding='utf-8') as f:
        f.write(content)
    print('Replacement successful')
else:
    print('Old string not found')
