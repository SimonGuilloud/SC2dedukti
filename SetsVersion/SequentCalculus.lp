require open lisa2dedukti.SetsVersion.FOL;
require open lisa2dedukti.SetsVersion.prelude;

// Deduction Rules
constant symbol Hypothesis (ϕ : Formula) (Γ Δ: SetF) : prf (seq (ϕ ** Γ) (ϕ ** Δ));
constant symbol Cut Γ Σ Δ Ω ϕ : prf (seq Γ (ϕ ** Δ)) → prf (seq (ϕ ** Σ) Ω) → prf (seq (Γ ∪ Σ) (Δ ∪ Ω));


symbol LeftAnd Γ l Δ : prf (seq (l ∪ Γ) Δ) → prf (seq ((set2and l) ** Γ) Δ);
symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ** Γ) Δ) → prf (seq  (ψ ** Σ) Ω) → prf (seq ((ϕ ∨ ψ) ** (Γ ∪ Σ)) (Δ ∪ Ω));
constant symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ** Δ)) → prf (seq (ψ ** Σ) Ω) → prf (seq ((Implies ϕ ψ) ** (Γ ∪ Σ)) (Δ ∪ Ω));
symbol LeftIff Γ ϕ ψ Δ : prf (seq ((Implies ϕ ψ) ** (Implies ψ ϕ) ** Γ) Δ) → prf (seq ((Iff ϕ ψ) ** Γ) Δ);
symbol LeftNot Γ ϕ Δ : prf (seq Γ (ϕ ** Δ)) → prf (seq ( (Neg ϕ) ** Γ) Δ);
constant symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ** Γ) Δ) → prf (seq ((Forall ϕ) ** Γ) Δ);
symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ** Γ) Δ)) → prf (seq ((Exists ϕ) ** Γ) Δ);
symbol LeftExistsOne Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ** Γ) Δ) → 
                                      prf (seq ((ExistsOne ϕ ** Γ)) Δ);


symbol RightAnd Γ Σ Δ Ω ϕ ψ : prf (seq Γ (ϕ ** Δ)) → prf (seq  Σ (ψ ** Ω)) → prf (seq (Γ ∪ Σ)  ((ϕ ∧ ψ) ** (Δ ∪ Ω)) );
symbol RightOr Γ l Δ : prf (seq Γ (l ∪ Δ)) → prf (seq Γ ((set2or l) ** Δ));
constant symbol RightImplies Γ ϕ ψ Δ : prf (seq (ϕ ** Γ) (ψ ** Δ)) → prf (seq Γ ((Implies ϕ ψ) ** Δ));
symbol RightIff Γ Σ Δ Ω ϕ ψ : prf (seq Γ ((Implies ϕ ψ) ** Δ)) → prf (seq  Σ ((Implies ψ ϕ) ** Ω)) → prf (seq (Γ ∪ Σ) ((Iff ϕ ψ) ** (Δ ∪ Ω)));
symbol RightNot Γ ϕ Δ : prf (seq (ϕ ** Γ) Δ) → prf (seq  Γ ((Neg ϕ) ** Δ));
constant symbol RightForall Γ ϕ Δ : (Π x:Term, prf (seq Γ ((ϕ x) ** Δ))) → prf (seq Γ ((Forall ϕ) ** Δ));
symbol RightExists Γ ϕ t Δ : prf (seq Γ ((ϕ t) ** Δ) ) → prf (seq Γ ((Exists ϕ) ** Δ));
symbol RightExistsOne Γ ϕ Δ : prf (seq Γ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ** Δ)) → 
                                      prf (seq Γ ((ExistsOne ϕ) ** Δ));

symbol LeftWeakening Σ Γ Δ : prf (seq Γ Δ) → prf (seq (Σ ∪ Γ) Δ);
symbol RightWeakening Γ Ω Δ : prf (seq Γ Δ) → prf (seq Γ (Ω ∪ Δ));

symbol LeftRefl Γ t Δ : prf (seq ((Equality t t) ** Γ) Δ) → prf (seq Γ Δ);
symbol RightRefl Γ t Δ : prf (seq Γ ((Equality t t) ** Δ)); // Check in LISA

symbol LeftSubstEq Γ ϕ Δ s t : prf (seq ((ϕ s) ** Γ) Δ) → prf (seq ((Equality s t) ** (ϕ t) ** Γ) Δ);
symbol LeftSubstIff Γ ϕ Δ a b : prf (seq ((ϕ a) ** Γ) Δ) → prf (seq ((Iff a b) ** (ϕ b) ** Γ) Δ);

symbol RightSubstEq Γ ϕ Δ s t : prf (seq Γ ((ϕ s) ** Δ)) → prf (seq ((Equality s t) ** Γ)  ((ϕ t) ** Δ));
symbol RightSubstIff Γ ϕ Δ a b : prf (seq Γ ((ϕ a) ** Δ)) → prf (seq ((Iff a b) ** Γ)  ((ϕ b) ** Δ));



/*
Rules for instantiating variables and schematic symbols
The rules are builtin in Sequent Calculus but when variables are mapped to 
Dedukti variables, it is a theorem of the (Dedukti) meta-logic
*/
opaque symbol InstTerm (sx : Term → Sequent) (t:Term) : (Π (x : Term), prf (sx x)) → prf (sx t) ≔ λ f, f t ;
opaque symbol InstFormula (sx : Formula → Sequent) (ϕ:Formula) : (Π (x : Formula), prf (sx x)) → prf (sx ϕ) ≔ λ f, f ϕ ;



