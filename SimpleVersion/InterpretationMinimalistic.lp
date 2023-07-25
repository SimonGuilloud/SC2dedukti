require open lisa2dedukti.SimpleVersion.FOL;
require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.SequentCalculus;

//Here we do layered interpretation in minimal logic

//First we interpret sequents with exactly one formula on the right into functions over formulas

injective symbol fprf : Formula → TYPE;

rule prf (Nil ⊧ ($x ⸬ Nil)) ↪ fprf ($x);
rule prf (($y ⸬ $l) ⊧ ($x ⸬ Nil)) ↪ (fprf $y) → prf ($l ⊧ ($x ⸬ Nil));

//Then we interpret Formulas of minimal logic over TYPES.

rule fprf (Implies $ϕ $ψ) ↪ fprf $ϕ → fprf $ψ;
rule fprf (Forall $P) ↪ Π x : Term, fprf ($P x);


//Minimalistic rules
//We translate structural rules, Cut and Implies and Forall rules in the case of minimal logic, i.e. when the right handside of a sequent contains exactly one formula.
//Minimalistic logic also uses ⊥, but has no dedicated axiom for it: It behaves like a free symbol.

//symbol Hypothesis ϕ Γ Δ : prf ((ϕ ⸬ Γ) (ϕ ⸬ Δ));
rule Hypothesis $ϕ Nil Nil ↪ λ x, x; //In the minimalistic case, Δ = Nil
rule Hypothesis $ϕ ($x ⸬ $Γ) Nil ↪ λ x y, Hypothesis $ϕ $Γ Nil x;

//symbol Swap2Left Γ Δ (n : Nat) : prf (Γ Δ) → prf ((swap2 Γ n) Δ);
rule Swap2Left Nil _ _ ↪ λ x, x;
rule Swap2Left ($x ⸬ Nil) _ _ ↪ λ x, x;
rule Swap2Left ($x ⸬ $y ⸬ $l) (_ ⸬ Nil) 0 ↪ λ p x y, p y x;
rule Swap2Left ($x ⸬ $y ⸬ $l) ($f ⸬ Nil) (S $n) ↪ λ p x, Swap2Left ($y ⸬ $l) ($f ⸬ Nil) $n (p x) ;
//symbol Swap2Right Γ Δ (n : Nat) : prf (Γ Δ) → prf (Γ (swap2 Δ n));
//In minimalistic logic, Swap2Right can only be trivial
rule Swap2Right _ (_ ⸬ Nil) _ ↪ λ x, x;


//symbol ContractLeft x Γ Δ : prf ((x ⸬ x ⸬ Γ) Δ) → prf ((x ⸬ Γ) Δ);
rule ContractLeft _ _ (_ ⸬ Nil) ↪ λ p px, p px px;
//symbol ContractRight x Γ Δ : prf (Γ (x ⸬ x ⸬ Δ) ) → prf (Γ (x ⸬ Δ));
//Can't be applied in minimal or intuitionistic logic.


//symbol LeftWeakening Σ Γ Δ : prf (Γ Δ) → prf ((append Σ Γ) Δ);
rule LeftWeakening Nil $Γ ($f ⸬ Nil) ↪ λ x, x;
rule LeftWeakening ($x ⸬ $Σ) $Γ ($f ⸬ Nil) ↪ λ p x, LeftWeakening $Σ $Γ ($f ⸬ Nil) p;
//symbol RightWeakening Γ Ω Δ : prf (Γ Δ) → prf (Γ (append Ω Δ));
//Can't be applied in minimal logic


//symbol Cut Γ Σ Δ Ω ϕ : prf (Γ (ϕ ⸬ Δ)) → prf ((ϕ ⸬ Σ) Ω) → prf ((append Γ Σ) (append Δ Ω));
rule Cut Nil $Σ Nil (_ ⸬ Nil) _ ↪ λ π1 π2, π2 π1; //In minimalistic logic, Δ = Nil and Ω = (_ ⸬ Nil)
rule Cut (_ ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ ↪ λ π1 π2 x, Cut $Γ $Σ Nil ($f ⸬ Nil) $ϕ (π1 x) π2;

//symbol RightImplies Γ ϕ ψ Δ : prf ((ϕ ⸬ Γ) (ψ ⸬ Δ)) → prf (Γ ((Implies ϕ ψ) ⸬ Δ));
rule RightImplies Nil $ϕ $ψ Nil ↪ λ p1 p2, p1 p2;
rule RightImplies (_ ⸬ $l) $ϕ $ψ Nil ↪ λ π x, (RightImplies $l $ϕ $ψ Nil) λ q, π q x ;
//symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (Γ (ϕ ⸬ Δ)) → prf ((ψ ⸬ Σ) Ω) → prf (((Implies ϕ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
rule LeftImplies Nil _ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ phi psif phipsi, psif (phipsi phi);
rule LeftImplies ($x ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ xpphi psipf phipsi x, LeftImplies $Γ $Σ Nil ($f ⸬ Nil) $ϕ $ψ (xpphi x) psipf phipsi;


//symbol RightForall Γ ϕ Δ : (Π x:Term, prf (Γ ((ϕ x) ⸬ Δ))) → prf (Γ ((Forall ϕ) ⸬ Δ));
rule RightForall Nil $ϕ Nil ↪ λ px, px;
rule RightForall ($x ⸬ $Γ) $ϕ Nil ↪ λ p px, RightForall $Γ $ϕ Nil (λ x1, p x1 px);
//symbol LeftForall Γ ϕ t Δ : prf (((ϕ t) ⸬ Γ) Δ) → prf (((Forall ϕ) ⸬ Γ) Δ);
rule LeftForall $Γ $ϕ $t ($f ⸬ Nil) ↪ λ px ax, px (ax $t);
