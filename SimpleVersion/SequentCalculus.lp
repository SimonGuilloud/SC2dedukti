require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.FOL;


// Deduction Rules
symbol Hypothesis ϕ Γ Δ : prf (seq (ϕ ⸬ Γ) (ϕ ⸬ Δ));

symbol SwapLeft Γ Δ (perm: (List nat)) : prf (seq Γ Δ) → prf (seq (permute perm Γ Nil) Δ);
symbol Swap2Left Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq (swap2 Γ n) Δ);
symbol SwapRight Γ Δ (perm: (List nat)) : prf (seq Γ Δ) → prf (seq Γ (permute perm Δ Nil));
symbol Swap2Right Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq Γ (swap2 Δ n));


symbol ContractLeft x Γ Δ : prf (seq (x ⸬ x ⸬ Γ) Δ) → prf (seq (x ⸬ Γ) Δ);
symbol ContractRight x Γ Δ : prf (seq Γ (x ⸬ x ⸬ Δ) ) → prf (seq Γ (x ⸬ Δ));

symbol Cut Γ Σ Δ Ω ϕ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ϕ ⸬ Σ) Ω) → prf (seq (append Γ Σ) (append Δ Ω));

symbol LeftAnd Γ ϕ ψ Δ : prf (seq (ϕ ⸬ ψ ⸬ Γ) Δ) → prf (seq ((ϕ ∧ ψ) ⸬ Γ) Δ);
symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  (ψ ⸬ Σ) Ω) → prf (seq ((ϕ ∨ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ψ ⸬ Σ) Ω) → prf (seq ((Implies ϕ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
symbol LeftIff Γ ϕ ψ Δ : prf (seq ((Implies ϕ ψ) ⸬ (Implies ψ ϕ) ⸬ Γ) Δ) → prf (seq ((Iff ϕ ψ) ⸬ Γ) Δ);
symbol LeftNot Γ ϕ Δ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq ( (Neg ϕ) ⸬ Γ) Δ);
symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ⸬ Γ) Δ) → prf (seq ((Forall ϕ) ⸬ Γ) Δ);
symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ⸬ Γ) Δ)) → prf (seq ((Exists ϕ) ⸬ Γ) Δ);
symbol LeftExistsOne Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Γ) Δ) → prf (seq ((ExistsOne ϕ ⸬ Γ)) Δ);

symbol RightAnd Γ Σ Δ Ω ϕ ψ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq  Σ (ψ ⸬ Ω)) → prf (seq (append Γ Σ) ((ϕ ∧ ψ) ⸬ (append Δ Ω)));
symbol RightOr Γ ϕ ψ Δ : prf (seq Γ (ϕ ⸬ ψ ⸬ Δ)) → prf (seq Γ ((ϕ ∨ ψ) ⸬ Δ));
symbol RightImplies Γ ϕ ψ Δ : prf (seq (ϕ ⸬ Γ) (ψ ⸬ Δ)) → prf (seq Γ ((Implies ϕ ψ) ⸬ Δ));
symbol RightIff Γ Σ Δ Ω ϕ ψ : prf (seq Γ ((Implies ϕ ψ) ⸬ Δ)) → prf (seq  Σ ((Implies ψ ϕ) ⸬ Ω)) → prf (seq (append Γ Σ) ((Iff ϕ ψ) ⸬ (append Δ Ω)));
symbol RightNot Γ ϕ Δ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  Γ ((Neg ϕ) ⸬ Δ));
symbol RightForall Γ ϕ Δ : (Π x:Term, prf (seq Γ ((ϕ x) ⸬ Δ))) → prf (seq Γ ((Forall ϕ) ⸬ Δ));
symbol RightExists Γ ϕ t Δ : prf (seq Γ ((ϕ t) ⸬ Δ) ) → prf (seq Γ ((Exists ϕ) ⸬ Δ));
symbol RightExistsOne Γ ϕ Δ : prf (seq Γ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Δ)) → prf (seq Γ ((ExistsOne ϕ) ⸬ Δ));

symbol LeftWeakening Σ Γ Δ : prf (seq Γ Δ) → prf (seq (append Σ Γ) Δ);
symbol RightWeakening Γ Ω Δ : prf (seq Γ Δ) → prf (seq Γ (append Ω Δ));

symbol LeftRefl Γ t Δ : prf (seq ((Equality t t) ⸬ Γ) Δ) → prf (seq Γ Δ);
symbol RightRefl t : prf (seq Nil ((Equality t t) ⸬ Nil));

symbol LeftSubstEq Γ ϕ Δ s t : prf (seq ((ϕ s) ⸬ Γ) Δ) → prf (seq ((Equality s t) ⸬ (ϕ t) ⸬ Γ) Δ);
symbol LeftSubstIff Γ ϕ Δ a b : prf (seq ((ϕ a) ⸬ Γ) Δ) → prf (seq ((Iff a b) ⸬ (ϕ b) ⸬ Γ) Δ);

symbol RightSubstEq Γ ϕ Δ s t : prf (seq Γ ((ϕ s) ⸬ Δ)) → prf (seq ((Equality s t) ⸬ Γ)  ((ϕ t) ⸬ Δ));
symbol RightSubstIff Γ ϕ Δ a b : prf (seq Γ ((ϕ a) ⸬ Δ)) → prf (seq ((Iff a b) ⸬ Γ)  ((ϕ b) ⸬ Δ));



/*
Rules for instantiating variables and schematic symbols
The rules are builtin in Sequent Calculus but when variables are mapped to 
Dedukti variables, it is a theorem of the (Dedukti) meta-logic
*/
opaque symbol InstTerm (sx : Term → Sequent) (t:Term) : (Π (x : Term), prf (sx x)) → prf (sx t) ≔ λ f, f t ;
opaque symbol InstFormula (sx : Formula → Sequent) (ϕ:Formula) : (Π (x : Formula), prf (sx x)) → prf (sx ϕ) ≔ λ f, f ϕ ;


