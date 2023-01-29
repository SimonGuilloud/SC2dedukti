require open lisa2dedukti.SetsVersion.FOL;
require open lisa2dedukti.SetsVersion.prelude;
require open lisa2dedukti.SetsVersion.SequentCalculus;


symbol pierce0 ϕ ≔ Hypothesis ϕ EmptyF EmptyF;

symbol pierce1 ϕ ψ ≔ (RightWeakening (ϕ ** EmptyF) (ψ ** EmptyF) (ϕ ** EmptyF) (pierce0 ϕ));

symbol pierce2 ϕ ψ ≔ (RightImplies EmptyF ϕ ψ (ϕ ** EmptyF) (pierce1 ϕ ψ) );

symbol pierce3 ϕ ψ ≔ (LeftImplies EmptyF EmptyF (ϕ ** EmptyF) (ϕ ** EmptyF) (Implies ϕ ψ) ϕ (pierce2 ϕ ψ) (Hypothesis ϕ EmptyF EmptyF));

symbol pierce4 ϕ ψ ≔ (RightImplies EmptyF (Implies (Implies ϕ ψ) ϕ) ϕ EmptyF (pierce3 ϕ ψ));




symbol russel1 ϕ ≔ Hypothesis ϕ EmptyF EmptyF;

symbol russel2 (ϕ : Formula) ≔ RightNot EmptyF ϕ (ϕ ** EmptyF) (russel1 ϕ);

symbol russel3 ϕ ≔ LeftImplies EmptyF EmptyF (ϕ ** EmptyF) (ϕ ** EmptyF) (Neg ϕ) ϕ (russel2 ϕ) (russel1 ϕ);

symbol d1 ϕ ≔ (Implies (Neg ϕ) ϕ);

symbol russel4 (ϕ: Formula) ≔ LeftNot ((d1 ϕ) ** EmptyF) ϕ EmptyF (russel3 ϕ) ;

symbol russel5 ϕ ≔ LeftImplies ((d1 ϕ) ** EmptyF) ((d1 ϕ) ** EmptyF) EmptyF EmptyF ϕ (Neg ϕ) (russel3 ϕ) (russel4 ϕ);

symbol russel6 ϕ ≔ LeftIff EmptyF (Neg ϕ) ϕ EmptyF (russel5 ϕ);

symbol russel7 y R : (prf (seq ((Forall (λ x, (Iff (Neg (R x x)) (R x y)))) ** EmptyF) EmptyF)) ≔ LeftForall EmptyF (λ x, (Iff (Neg (R x x)) (R x y))) y EmptyF (russel6 (R y y));

