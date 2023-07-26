require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.FOL;


// Deduction Rules
symbol Hypothesis ϕ Γ Δ : prf ((ϕ ⸬ Γ) ⊧ (ϕ ⸬ Δ));

symbol SwapLeft Γ Δ (perm: (List nat)) : prf (Γ ⊧ Δ) → prf ((permute perm Γ Nil) ⊧ Δ);
symbol Swap2Left Γ Δ (n : Nat) : prf (Γ ⊧ Δ) → prf ((swap2 Γ n) ⊧ Δ);
symbol SwapRight Γ Δ (perm: (List nat)) : prf (Γ ⊧ Δ) → prf (Γ ⊧ (permute perm Δ Nil));
symbol Swap2Right Γ Δ (n : Nat) : prf (Γ ⊧ Δ) → prf (Γ ⊧ (swap2 Δ n));


symbol ContractLeft x Γ Δ : prf ((x ⸬ x ⸬ Γ) ⊧ Δ) → prf ((x ⸬ Γ) ⊧ Δ);
symbol ContractRight x Γ Δ : prf (Γ ⊧ (x ⸬ x ⸬ Δ) ) → prf (Γ ⊧ (x ⸬ Δ));

symbol Cut Γ Σ Δ Ω ϕ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf ((ϕ ⸬ Σ) ⊧ Ω) → prf ((append Γ Σ) ⊧ (append Δ Ω));

symbol LeftAnd1 Γ ϕ ψ Δ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf (((ϕ ∧ ψ) ⸬ Γ) ⊧ Δ);
symbol LeftAnd2 Γ ϕ ψ Δ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf (((ψ ∧ ϕ) ⸬ Γ) ⊧ Δ);
symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf ( (ψ ⸬ Σ) ⊧ Ω) → prf (((ϕ ∨ ψ) ⸬ (append Γ Σ)) ⊧ (append Δ Ω));
symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (Γ ⊧ (ϕ ⸬ Δ)) → prf ((ψ ⸬ Σ) ⊧ Ω) → prf (((Implies ϕ ψ) ⸬ (append Γ Σ)) ⊧ (append Δ Ω));
symbol LeftIff Γ ϕ ψ Δ : prf (((Implies ϕ ψ) ⸬ (Implies ψ ϕ) ⸬ Γ) ⊧ Δ) → prf (((Iff ϕ ψ) ⸬ Γ) ⊧ Δ);
symbol LeftNot Γ ϕ Δ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf (( (Neg ϕ) ⸬ Γ) ⊧ Δ);
symbol LeftForall Γ ϕ t Δ : prf (((ϕ t) ⸬ Γ) ⊧ Δ) → prf (((Forall ϕ) ⸬ Γ) ⊧ Δ);
symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (((ϕ x) ⸬ Γ) ⊧ Δ)) → prf (((Exists ϕ) ⸬ Γ) ⊧ Δ);
symbol LeftExistsOne Γ ϕ Δ : prf (((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Γ) ⊧ Δ) → prf (((ExistsOne ϕ ⸬ Γ)) ⊧ Δ);

symbol RightAnd Γ Σ Δ Ω ϕ ψ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf ( Σ ⊧ (ψ ⸬ Ω)) → prf ((append Γ Σ) ⊧ ((ϕ ∧ ψ) ⸬ (append Δ Ω)));
symbol RightOr1 Γ ϕ ψ Δ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf (Γ ⊧ ((ϕ ∨ ψ) ⸬ Δ));
symbol RightOr2 Γ ϕ ψ Δ : prf (Γ ⊧ (ϕ ⸬ Δ)) → prf (Γ ⊧ ((ψ ∨ ϕ) ⸬ Δ));
symbol RightImplies Γ ϕ ψ Δ : prf ((ϕ ⸬ Γ) ⊧ (ψ ⸬ Δ)) → prf (Γ ⊧ ((Implies ϕ ψ) ⸬ Δ));
symbol RightIff Γ Σ Δ Ω ϕ ψ : prf (Γ ⊧ ((Implies ϕ ψ) ⸬ Δ)) → prf (Σ ⊧ ((Implies ψ ϕ) ⸬ Ω)) → prf ((append Γ Σ) ⊧ ((Iff ϕ ψ) ⸬ (append Δ Ω)));
symbol RightNot Γ ϕ Δ : prf ((ϕ ⸬ Γ) ⊧ Δ) → prf (Γ ⊧ ((Neg ϕ) ⸬ Δ));
symbol RightForall Γ ϕ Δ : (Π x:Term, prf (Γ ⊧ ((ϕ x) ⸬ Δ))) → prf (Γ ⊧ ((Forall ϕ) ⸬ Δ));
symbol RightExists Γ ϕ t Δ : prf (Γ ⊧ ((ϕ t) ⸬ Δ) ) → prf (Γ ⊧ ((Exists ϕ) ⸬ Δ));
symbol RightExistsOne Γ ϕ Δ : prf (Γ ⊧ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Δ)) → prf (Γ ⊧ ((ExistsOne ϕ) ⸬ Δ));

symbol LeftWeakening Σ Γ Δ : prf (Γ ⊧ Δ) → prf ((append Σ Γ) ⊧ Δ);
symbol RightWeakening Γ Ω Δ : prf (Γ ⊧ Δ) → prf (Γ ⊧ (append Ω Δ));

symbol LeftRefl Γ t Δ : prf (((Equality t t) ⸬ Γ) ⊧ Δ) → prf (Γ ⊧ Δ);
symbol RightRefl t : prf (Nil ⊧ ((Equality t t) ⸬ Nil));

symbol LeftSubstEq Γ ϕ Δ s t : prf (((ϕ s) ⸬ Γ) ⊧ Δ) → prf (((Equality s t) ⸬ (ϕ t) ⸬ Γ) ⊧ Δ);
symbol LeftSubstIff Γ ϕ Δ a b : prf (((ϕ a) ⸬ Γ) ⊧ Δ) → prf (((Iff a b) ⸬ (ϕ b) ⸬ Γ) ⊧ Δ);

symbol RightSubstEq Γ ϕ Δ s t : prf (Γ ⊧ ((ϕ s) ⸬ Δ)) → prf (((Equality s t) ⸬ Γ) ⊧ ((ϕ t) ⸬ Δ));
symbol RightSubstIff Γ ϕ Δ a b : prf (Γ ⊧ ((ϕ a) ⸬ Δ)) → prf (((Iff a b) ⸬ Γ) ⊧ ((ϕ b) ⸬ Δ));



/*
Rules for instantiating variables and schematic symbols
The rules are builtin in Sequent Calculus but when variables are mapped to 
Dedukti variables, it is a theorem of the (Dedukti) meta-logic
*/
opaque symbol InstTerm (sx : Term → Sequent) (t:Term) : (Π (x : Term), prf (sx x)) → prf (sx t) ≔ λ f, f t ;
opaque symbol InstFormula (sx : Formula → Sequent) (ϕ:Formula) : (Π (x : Formula), prf (sx x)) → prf (sx ϕ) ≔ λ f, f ϕ ;


