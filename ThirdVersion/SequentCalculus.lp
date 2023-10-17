require open lisa2dedukti.ThirdVersion.prelude;
require open lisa2dedukti.ThirdVersion.FOL;


// The weak rules

symbol Hypothesis ϕ: prf ((ϕ ⸬ Nil) ⊧ (ϕ ⸬ Nil));
symbol LeftWeakening ϕ Γ Δ : prf (Γ ⊧ Δ) → prf ((ϕ ⸬ Γ) ⊧ Δ);
symbol RightWeakening ϕ Γ Δ : prf (Γ ⊧ Δ) → prf (Γ ⊧ (ϕ ⸬ Δ));


// The strong rules

symbol Cut Γ1 Γ2 Δ1 Δ2 ϕ : prf (Γ1 ⊧ (ϕ ⸬ Δ1)) → prf ((ϕ ⸬ Γ2) ⊧ Δ2) → prf ((Γ1 u Γ2) ⊧ (Δ1 u Δ2));

symbol Left0 : prf ((Bot ⸬ Nil) ⊧ Nil);
symbol LeftAnd Γ ϕ ψ Δ : prf ((ϕ ⸬ ψ ⸬ Γ) ⊧ Δ) → prf (((ϕ ∧ ψ) ⸬ Γ) ⊧ Δ);
symbol LeftOr Γ Δ ϕ ψ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf ( (ψ ⸬ Γ) ⊧ Δ) → prf (((ϕ ∨ ψ) ⸬ Γ) ⊧ Δ);
symbol LeftNot Γ ϕ Δ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf (( (Neg ϕ) ⸬ Γ) ⊧ Δ);
symbol LeftImplies Γ Δ1 Δ2 ϕ ψ :  prf (Γ ⊧ (ϕ ⸬ Δ1)) → prf ((ψ ⸬ Γ) ⊧ Δ2) → prf (((Implies ϕ ψ) ⸬ Γ) ⊧ (Δ1 u Δ2));
//symbol LeftForall Γ ϕ t Δ : prf (((ϕ t) ⸬ Γ) ⊧ Δ) → prf (((Forall ϕ) ⸬ Γ) ⊧ Δ);
//symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (((ϕ x) ⸬ Γ) ⊧ Δ)) → prf (((Exists ϕ) ⸬ Γ) ⊧ Δ);

symbol Right1 : prf (Nil ⊧ (Top ⸬ Nil));
symbol RightAnd Γ Δ ϕ ψ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf ( Γ ⊧ (ψ ⸬ Δ)) → prf (Γ ⊧ ((ϕ ∧ ψ) ⸬ Δ));
symbol RightOr Γ ϕ ψ Δ : prf (Γ ⊧ (ϕ ⸬ ψ ⸬ Δ)) → prf (Γ ⊧ ((ϕ ∨ ψ) ⸬ Δ));
symbol RightNot Γ ϕ Δ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf (Γ ⊧ ((Neg ϕ) ⸬ Δ));
symbol RightImplies Γ ϕ ψ Δ : prf ((ϕ ⸬ Γ) ⊧ (ψ ⸬ Δ)) → prf (Γ ⊧ ((Implies ϕ ψ) ⸬ Δ));
//symbol RightForall Γ ϕ Δ : (Π x:Term, prf (Γ ⊧ ((ϕ x) ⸬ Δ))) → prf (Γ ⊧ ((Forall ϕ) ⸬ Δ));
//symbol RightExists Γ ϕ t Δ : prf (Γ ⊧ ((ϕ t) ⸬ Δ) ) → prf (Γ ⊧ ((Exists ϕ) ⸬ Δ));


//symbol LeftRefl Γ t Δ : prf (((Equality t t) ⸬ Γ) ⊧ Δ) → prf (Γ ⊧ Δ);
//symbol RightRefl t : prf (Nil ⊧ ((Equality t t) ⸬ Nil));

//symbol LeftSubstEq Γ ϕ Δ s t : prf (((ϕ s) ⸬ Γ) ⊧ Δ) → prf (((Equality s t) ⸬ (ϕ t) ⸬ Γ) ⊧ Δ);
//symbol LeftSubstIff Γ ϕ Δ a b : prf (((ϕ a) ⸬ Γ) ⊧ Δ) → prf (((Iff a b) ⸬ (ϕ b) ⸬ Γ) ⊧ Δ);

//symbol RightSubstEq Γ ϕ Δ s t : prf (Γ ⊧ ((ϕ s) ⸬ Δ)) → prf (((Equality s t) ⸬ Γ) ⊧ ((ϕ t) ⸬ Δ));
//symbol RightSubstIff Γ ϕ Δ a b : prf (Γ ⊧ ((ϕ a) ⸬ Δ)) → prf (((Iff a b) ⸬ Γ) ⊧ ((ϕ b) ⸬ Δ));

// Interpretation of formulas in TYPES

injective symbol fprf : Formula → TYPE;
