require open lisa2dedukti.SimpleVersion.FOL;
require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.SequentCalculus;


symbol pierce0 ϕ ≔ Hypothesis ϕ Nil Nil;

symbol pierce1 ϕ ψ ≔ (RightWeakening (ϕ ⸬ Nil) (ψ ⸬ Nil) (ϕ ⸬ Nil) (pierce0 ϕ));

symbol pierce2 ϕ ψ ≔ (RightImplies Nil ϕ ψ (ϕ ⸬ Nil) (pierce1 ϕ ψ) );

symbol pierce3 ϕ ψ ≔ (LeftImplies Nil Nil (ϕ ⸬ Nil) (ϕ ⸬ Nil) (Implies ϕ ψ) ϕ (pierce2 ϕ ψ) (Hypothesis ϕ Nil Nil));

symbol pierce4 ϕ ψ ≔ (RightImplies Nil (Implies (Implies ϕ ψ) ϕ) ϕ Nil (pierce3 ϕ ψ));




symbol russel1 ϕ ≔ Hypothesis ϕ Nil Nil;

symbol russel2 (ϕ : Formula) ≔ RightNot Nil ϕ (ϕ ⸬ Nil) (russel1 ϕ);

symbol russel3 ϕ ≔ LeftImplies Nil Nil (ϕ ⸬ Nil) (ϕ ⸬ Nil) (Neg ϕ) ϕ (russel2 ϕ) (russel1 ϕ);

symbol d1 ϕ ≔ (Implies (Neg ϕ) ϕ);

symbol russel4 (ϕ: Formula) ≔ LeftNot ((d1 ϕ) ⸬ Nil) ϕ Nil (russel3 ϕ) ;

symbol russel5 ϕ ≔ LeftImplies ((d1 ϕ) ⸬ Nil) ((d1 ϕ) ⸬ Nil) Nil Nil ϕ (Neg ϕ) (russel3 ϕ) (russel4 ϕ);

symbol russel6 (ϕ: Formula) ≔ SwapLeft ((Implies ϕ (Neg ϕ)) ⸬ (d1 ϕ) ⸬ (d1 ϕ) ⸬ Nil) Nil (2 ⸬ 1 ⸬ 0 ⸬ Nil) (russel5 ϕ);

symbol russel7 ϕ ≔ LeftIff Nil (Neg ϕ) ϕ Nil (russel6 ϕ);

symbol russel8 y R : (prf (seq ((Forall (λ x, (Iff (Neg (R x x)) (R x y)))) ⸬ Nil) Nil)) ≔ LeftForall Nil (λ x, (Iff (Neg (R x x)) (R x y))) y Nil (russel7 (R y y)) ;

