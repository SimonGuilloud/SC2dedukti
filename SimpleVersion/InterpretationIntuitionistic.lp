require open lisa2dedukti.SimpleVersion.FOL;
require open lisa2dedukti.SimpleVersion.prelude;
require open lisa2dedukti.SimpleVersion.SequentCalculus;
require open lisa2dedukti.SimpleVersion.InterpretationMinimalistic;

//Here we extend the minimal logic interpretation to intuitionistic logic

//First, we need to interpret Sequents with 0 elements on the right hand side

//injective symbol fprf : Formula → TYPE;
rule prf ($Γ ⊧ Nil) ↪ prf ($Γ ⊧ (Bot ⸬ Nil));
//Then, we interpret formulas with multiple formulas on the right hand side
rule prf (Nil ⊧ ($x ⸬ $y ⸬ $Δ)) ↪ prf (Nil ⊧ (($x ∨ $y) ⸬ $Δ));
rule prf (($z ⸬ $l) ⊧ ($x ⸬ $y ⸬ $Δ)) ↪ (fprf $z) → prf ($l ⊧ ($x ⸬ $y ⸬ $Δ));

//One characterization of intuitionistic logic is that no strong rule has a conclusion whose 
//right hand side contains more than 2 formulas

//Implies and Forall are already interpreted in the minimal fragment, we interpret other symbols using impredicative definitions.

//rule fprf (Implies $ϕ $ψ) ↪ fprf $ϕ → fprf $ψ;
//rule fprf (Forall $P) ↪ Π x : Term, fprf ($P x);

rule fprf (Equality $x $y) ↪ Π r : Term → Formula, fprf (r $x) → fprf (r $y);

rule fprf Top ↪ Π f, (fprf f) → (fprf f);
rule fprf Bot ↪ Π f, fprf f;

rule fprf ($ϕ ∧ $ψ) ↪ Π γ, (fprf $ϕ → fprf $ψ → fprf γ) → fprf γ;
rule fprf ($ϕ ∨ $ψ) ↪ Π γ, (fprf $ϕ → fprf γ) → (fprf $ψ → fprf γ) → fprf γ;
rule fprf (Exists $p) ↪  Π r, (Π x, (fprf ($p x) → fprf r)) → fprf r;

rule fprf (Neg $ϕ) ↪ fprf (Implies $ϕ Bot);
rule fprf (Iff $ϕ $ψ) ↪ fprf ((Implies $ϕ $ψ) ∧ (Implies $ψ $ϕ));
rule fprf (ExistsOne $p) ↪ fprf (Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) ($p x))))));


//To show  the rule of substitution of equivalent formulas, we need to add the axiom of Propositional Extensionality.
symbol PropEq ≔ λ ϕ ψ, (Π r: Formula → Formula, fprf (r ϕ) → fprf (r ψ));
symbol PropExt : Π ϕ ψ, (fprf (Iff ϕ ψ)) → PropEq ϕ ψ;

//Lemmas about symetry of Equality and Iff are needed to reduce substitution rules.
symbol symEq : Π s t,  fprf (Equality s t) → fprf (Equality t s) ≔ λ s t eqst, eqst (λ y, Equality y s) (λ r i, i);
symbol symPropEq : Π f g,  PropEq f g → PropEq g f ≔ λ f g eqfg, PropExt g f (eqfg (λ y, Iff y f) (λ γ p, p (λ x, x) (λ x, x)));






//Intuitionistic rules
//We extend the minimalistic interpretation with:
//  a. Cases where the right-hand-side of the conclusion sequents of strong rules contains at most 1 unique element (i.e. if it contains 2 formulas, they must be the same formulas)
//  b. Rules for all symbols


//      Weak rules (structural)

//symbol Hypothesis ϕ Γ Δ : prf (seq (ϕ ⸬ Γ) (ϕ ⸬ Δ));
//rule Hypothesis $ϕ Nil Nil ↪ λ x, x;
//rule Hypothesis $ϕ ($x ⸬ $Γ) Nil ↪ λ x y, Hypothesis $ϕ $Γ Nil x;
//Same as minimalistic case

//symbol Swap2Left Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq (swap2 Γ n) Δ);
//rule Swap2Left Nil _ _ ↪ λ x, x;
//rule Swap2Left ($x ⸬ Nil) _ _ ↪ λ x, x;
//rule Swap2Left ($x ⸬ $y ⸬ $l) (_ ⸬ Nil) 0 ↪ λ p x y, p y x;
//rule Swap2Left ($x ⸬ $y ⸬ $l) ($f ⸬ Nil) (S $n) ↪ λ p x, Swap2Left ($y ⸬ $l) ($f ⸬ Nil) $n (p x) ;
rule Swap2Left ($x ⸬ $y ⸬ $l) Nil (S $n) ↪ λ p x, Swap2Left ($y ⸬ $l) Nil $n (p x) ;
//symbol Swap2Right Γ Δ (n : Nat) : prf (seq Γ Δ) → prf (seq Γ (swap2 Δ n));
//In minimalistic and Intuitionistic logic, Swap2Right can only be trivial

//rule Swap2Right _ (_ ⸬ Nil) _ ↪ λ x, x;
rule Swap2Right _ Nil _ ↪ λ x, x;
rule Swap2Right Nil ($x ⸬ $y ⸬ Nil) 0 ↪ λ f d a b, f d b a;
rule Swap2Right Nil ($x ⸬ $y ⸬ Nil) (S $n) ↪ λ x, x;


//symbol ContractLeft x Γ Δ : prf (seq (x ⸬ x ⸬ Γ) Δ) → prf (seq (x ⸬ Γ) Δ);
//rule ContractLeft _ _ (_ ⸬ Nil) ↪ λ p px, p px px;
//symbol ContractRight x Γ Δ : prf (seq Γ (x ⸬ x ⸬ Δ) ) → prf (seq Γ (x ⸬ Δ));
rule ContractRight $x Nil Nil ↪ λ (disj : (Π γ: Formula, (fprf $x → fprf γ) → (fprf $x → fprf γ) → fprf γ)), disj $x (λ i, i) (λ i, i);


//symbol LeftWeakening Σ Γ Δ : prf (seq Γ Δ) → prf (seq (append Σ Γ) Δ);
//rule LeftWeakening Nil $Γ ($f ⸬ Nil) ↪ λ x, x;
//rule LeftWeakening ($x ⸬ $Σ) $Γ ($f ⸬ Nil) ↪ λ p x, LeftWeakening $Σ $Γ ($f ⸬ Nil) p;
rule LeftWeakening Nil $Γ Nil ↪ λ x, x;
rule LeftWeakening ($x ⸬ $Σ) $Γ Nil ↪ λ p x, LeftWeakening $Σ $Γ Nil p;
//symbol RightWeakening Γ Ω Δ : prf (seq Γ Δ) → prf (seq Γ (append Ω Δ));
rule RightWeakening $Γ Nil Nil ↪ λ x, x;
rule RightWeakening $Γ Nil ($g ⸬ Nil) ↪ λ x, x;
rule RightWeakening Nil ($f ⸬ Nil) Nil ↪ λ bot, (bot $f);
rule RightWeakening ($x ⸬ $Γ) ($f ⸬ Nil) Nil ↪ λ p x, RightWeakening $Γ ($f ⸬ Nil) Nil (p x); 
rule RightWeakening Nil ($f ⸬ Nil) ($g ⸬ Nil) ↪ λ g f p1 p2, p2 g;
rule RightWeakening ($x ⸬ $Γ) ($f ⸬ Nil) ($g ⸬ Nil) ↪ λ p x, RightWeakening $Γ ($f ⸬ Nil) ($g ⸬ Nil) (p x); 


//        Strong Rules



//    Left Rules

//symbol Cut Γ Σ Δ Ω ϕ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ϕ ⸬ Σ) Ω) → prf (seq (append Γ Σ) (append Δ Ω));
//rule Cut Nil _ Nil (_ ⸬ Nil) _ ↪ λ π1 π2, π2 π1; //In minimalistic logic, Δ = Nil and Ω = (_ ⸬ Nil)
//rule Cut (_ ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ ↪ λ π1 π2 x, Cut $Γ $Σ Nil ($f ⸬ Nil) $ϕ (π1 x) π2;
rule Cut Nil _ Nil Nil _ ↪ λ x y, y x;
rule Cut (_ ⸬ $Γ) $Σ Nil Nil $ϕ ↪ λ π1 π2 x, Cut $Γ $Σ Nil Nil $ϕ (π1 x) π2;


//symbol LeftAnd Γ ϕ ψ Δ : prf (seq (ϕ ⸬ ψ ⸬ Γ) Δ) → prf (seq ((ϕ ∧ ψ) ⸬ Γ) Δ);
rule LeftAnd Nil $ϕ $ψ Nil ↪ λ p c, c Bot p;
rule LeftAnd ($x ⸬ $Γ) $ϕ $ψ Nil ↪ λ p c x, LeftAnd $Γ $ϕ $ψ Nil (λ phi psi, p phi psi x) c;
rule LeftAnd Nil $ϕ $ψ ($f ⸬ Nil) ↪ λ p c, c $f p;
rule LeftAnd ($x ⸬ $Γ) $ϕ $ψ ($f ⸬ Nil) ↪ λ p c x, LeftAnd $Γ $ϕ $ψ ($f ⸬ Nil) (λ phi psi, p phi psi x) c;


//symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  (ψ ⸬ Σ) Ω) → prf (seq ((ϕ ∨ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
//We need the for different cases on Δ and Ω, and for each the base case and the inductions on Σ and Γ, for a total of 12 cases.
rule LeftOr Nil Nil Nil Nil $ϕ $ψ ↪ λ p1 p2 d, (d Bot p1 p2);
rule LeftOr Nil ($y ⸬ $Σ) Nil Nil  $ϕ $ψ ↪ λ p1 p2 d y, LeftOr Nil $Σ Nil Nil $ϕ $ψ p1 (λ phi, p2 phi y) d;
rule LeftOr ($x ⸬ $Γ) $Σ Nil Nil  $ϕ $ψ ↪ λ p1 p2 d x, LeftOr $Γ $Σ Nil Nil $ϕ $ψ (λ phi, p1 phi x) p2 d;

rule LeftOr Nil Nil Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 (d: (Π γ: Formula, (fprf $ϕ → fprf γ) → (fprf $ψ → fprf γ) → fprf γ)), (d $f (λ pphi, (p1 pphi $f)) p2);
rule LeftOr Nil ($y ⸬ $Σ) Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 d y, LeftOr Nil $Σ Nil ($f ⸬ Nil) $ϕ $ψ p1 (λ phi, p2 phi y) d;
rule LeftOr ($x ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 d x, LeftOr $Γ $Σ Nil ($f ⸬ Nil) $ϕ $ψ (λ phi, p1 phi x) p2 d;

rule LeftOr Nil Nil ($f ⸬ Nil) Nil $ϕ $ψ ↪ λ p1 p2 (d: (Π γ: Formula, (fprf $ϕ → fprf γ) → (fprf $ψ → fprf γ) → fprf γ)), (d $f p1 (λ pphi, (p2 pphi $f)) );
rule LeftOr Nil ($y ⸬ $Σ) ($f ⸬ Nil) Nil $ϕ $ψ ↪ λ p1 p2 d y, LeftOr Nil $Σ ($f ⸬ Nil) Nil $ϕ $ψ p1 (λ phi, p2 phi y) d;
rule LeftOr ($x ⸬ $Γ) $Σ ($f ⸬ Nil) Nil $ϕ $ψ ↪ λ p1 p2 d x, LeftOr $Γ $Σ ($f ⸬ Nil) Nil $ϕ $ψ (λ phi, p1 phi x) p2 d;

rule LeftOr Nil Nil ($f ⸬ Nil) ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 d a b c, b (d $f p1 p2);
rule LeftOr Nil ($y ⸬ $Σ) ($f ⸬ Nil) ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 d y, LeftOr Nil $Σ ($f ⸬ Nil) ($f ⸬ Nil) $ϕ $ψ p1 (λ phi, p2 phi y) d;
rule LeftOr ($x ⸬ $Γ) $Σ ($f ⸬ Nil) ($f ⸬ Nil) $ϕ $ψ ↪ λ p1 p2 d x, LeftOr $Γ $Σ ($f ⸬ Nil) ($f ⸬ Nil) $ϕ $ψ (λ phi, p1 phi x) p2 d;

//symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ψ ⸬ Σ) Ω) → prf (seq ((Implies ϕ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
//rule LeftImplies Nil _ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ phi psif phipsi, psif (phipsi phi);
//rule LeftImplies ($x ⸬ $Γ) $Σ Nil ($f ⸬ Nil) $ϕ $ψ ↪ λ xpphi psipf phipsi x, LeftImplies $Γ $Σ Nil ($f ⸬ Nil) $ϕ $ψ (xpphi x) psipf phipsi;
rule LeftImplies $Γ $Σ Nil Nil $ϕ $ψ ↪ LeftImplies $Γ $Σ Nil (Bot ⸬ Nil) $ϕ $ψ;

//symbol LeftIff Γ ϕ ψ Δ : prf (seq ((Implies ϕ ψ) ⸬ (Implies ψ ϕ) ⸬ Γ) Δ) → prf (seq ((Iff ϕ ψ) ⸬ Γ) Δ);
rule LeftIff $Γ $ϕ $ψ Nil ↪ LeftAnd $Γ (Implies $ϕ $ψ) (Implies $ψ $ϕ) Nil;
rule LeftIff $Γ $ϕ $ψ ($f ⸬ Nil) ↪ LeftAnd $Γ (Implies $ϕ $ψ) (Implies $ψ $ϕ) ($f ⸬ Nil);
//symbol LeftNot Γ ϕ Δ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq ( (Neg ϕ) ⸬ Γ) Δ);
rule LeftNot Nil $ϕ Nil ↪ λ pf pff, pff pf; 
rule LeftNot ($x ⸬ $Γ) $ϕ Nil ↪ λ pr pf x, LeftNot $Γ $ϕ Nil (pr x) pf ; 
//symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ⸬ Γ) Δ) → prf (seq ((Forall ϕ) ⸬ Γ) Δ);
//rule LeftForall $Γ $ϕ $t ($f ⸬ Nil) ↪ λ px ax, px (ax $t);
rule LeftForall $Γ $ϕ $t Nil ↪ λ px ax, px (ax $t);
//LeftExists Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ⸬ Γ) Δ)) → prf (seq ((Exists ϕ) ⸬ Γ) Δ);
rule LeftExists Nil $ϕ Nil ↪ λ p pef, pef Bot p;
rule LeftExists ($x ⸬ $Γ) $ϕ Nil ↪ λ p pef f, LeftExists $Γ $ϕ Nil  (λ x prphix, p x prphix f) pef;
rule LeftExists Nil $ϕ ($f ⸬ Nil) ↪ λ p pef, pef $f p;
rule LeftExists ($f ⸬ $Γ) $ϕ ($f ⸬ Nil) ↪ λ p pef f, LeftExists $Γ $ϕ ($f ⸬ Nil) (λ x prphix, p x prphix f) pef;
//symbol LeftExistsOne Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Γ) Δ) → prf (seq ((ExistsOne ϕ ⸬ Γ)) Δ);
rule LeftExistsOne $Γ $ϕ Nil ↪ λ (p : prf (seq (Exists (λ y, Forall (λ x, Iff (Equality x y) ($ϕ x))) ⸬ $Γ) Nil)), p;



//     Right Rules

//symbol RightAnd Γ Σ Δ Ω ϕ ψ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq  Σ (ψ ⸬ Ω)) → prf (seq (append Γ Σ) ((ϕ ∧ ψ) ⸬ (append Δ Ω)));
rule RightAnd Nil Nil Nil Nil $ϕ $ψ ↪ λ p1 p2 f conj, (conj p1 p2);
rule RightAnd Nil ($y ⸬ $Σ) Nil Nil $ϕ $ψ ↪ λ p1 p2 y, RightAnd Nil $Σ Nil Nil $ϕ $ψ p1 (p2 y);
rule RightAnd ($x ⸬ $Γ) $Σ Nil Nil $ϕ $ψ ↪ λ p1 p2 x, RightAnd $Γ $Σ Nil Nil $ϕ $ψ (p1 x) p2;
//symbol RightOr Γ ϕ ψ Δ : prf (seq Γ (ϕ ⸬ ψ ⸬ Δ)) → prf (seq Γ ((ϕ ∨ ψ) ⸬ Δ));
rule RightOr Nil $ϕ $ψ Nil ↪ λ i, i;
rule RightOr ($x ⸬ $Γ) $ϕ $ψ Nil ↪ λ p x, RightOr $Γ $ϕ $ψ Nil (p x);

//symbol RightImplies Γ ϕ ψ Δ : prf (seq (ϕ ⸬ Γ) (ψ ⸬ Δ)) → prf (seq Γ ((Implies ϕ ψ) ⸬ Δ));
//same as minimalistic

//symbol RightIff Γ Σ Δ Ω ϕ ψ : prf (seq Γ ((Implies ϕ ψ) ⸬ Δ)) → prf (seq  Σ ((Implies ψ ϕ) ⸬ Ω)) → prf (seq (append Γ Σ) ((Iff ϕ ψ) ⸬ (append Δ Ω)));
rule RightIff Nil Nil Nil Nil $ϕ $ψ ↪ RightAnd Nil Nil Nil Nil (Implies $ϕ $ψ) (Implies $ψ $ϕ);
rule RightIff Nil ($y ⸬ $Σ) Nil Nil $ϕ $ψ ↪ λ p1 p2 y, RightIff Nil $Σ Nil Nil $ϕ $ψ p1 (p2 y);
rule RightIff ($x ⸬ $Γ) $Σ Nil Nil $ϕ $ψ ↪ λ p1 p2 x, RightIff $Γ $Σ Nil Nil $ϕ $ψ (p1 x) p2;

//symbol RightNot Γ ϕ Δ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  Γ ((Neg ϕ) ⸬ Δ));
rule RightNot Nil $ϕ Nil ↪ λ i, i;
rule RightNot ($x ⸬ $Γ) $ϕ Nil ↪ λ p x , RightNot $Γ $ϕ Nil (λ phi, p phi x);

//symbol RightForall Γ ϕ Δ : (Π x:Term, prf (seq Γ ((ϕ x) ⸬ Δ))) → prf (seq Γ ((Forall ϕ) ⸬ Δ));
//rule RightForall Nil $ϕ Nil ↪ λ px, px;
//rule RightForall ($x ⸬ $Γ) $ϕ Nil ↪ λ p px, RightForall $Γ $ϕ Nil (λ x1, p x1 px);
//Same as intuitionistic

//symbol RightExists Γ ϕ t Δ : prf (seq Γ ((ϕ t) ⸬ Δ) ) → prf (seq Γ ((Exists ϕ) ⸬ Δ));
rule RightExists Nil $ϕ $t Nil ↪ λ pphit r pr, pr $t pphit;
rule RightExists ($x ⸬ $Γ) $ϕ $t Nil ↪ λ p x , RightExists $Γ $ϕ $t Nil (p x);

//symbol RightExistsOne Γ ϕ Δ : prf (seq Γ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Δ)) → prf (seq Γ ((ExistsOne ϕ) ⸬ Δ));
rule RightExistsOne Nil $ϕ Nil ↪ λ p, p;
rule RightExistsOne ($x ⸬ $Γ) $ϕ Nil ↪ λ p x, RightExistsOne $Γ $ϕ Nil (p x);


//    EQUALITY
//symbol LeftRefl Γ t Δ : prf (seq ((Equality t t) ⸬ Γ) Δ) → prf (seq Γ Δ);
rule LeftRefl Nil $t Nil ↪ λ p, p (λ r i, i);
rule LeftRefl ($x ⸬ $Γ) $t Nil ↪ λ p x, LeftRefl $Γ $t Nil (λ a, p a x);

//symbol RightRefl t : prf (seq Nil ((Equality t t) ⸬ Nil));
rule RightRefl $t ↪ (λ r i, i);

//symbol LeftSubstEq Γ ϕ Δ s t : prf (seq ((ϕ s) ⸬ Γ) Δ) → prf (seq ((Equality s t) ⸬ (ϕ t) ⸬ Γ) Δ);
rule LeftSubstEq Nil $ϕ Nil $s $t ↪ λ p eq phit,  p ((symEq $s $t eq) $ϕ phit);
rule LeftSubstEq ($x ⸬ $Γ) $ϕ Nil $s $t ↪ λ p eq phi x, LeftSubstEq $Γ $ϕ Nil $s $t (λ a, p a x) eq phi;

//symbol RightSubstEq Γ ϕ Δ s t : prf (seq Γ ((ϕ s) ⸬ Δ)) → prf (seq ((Equality s t) ⸬ Γ)  ((ϕ t) ⸬ Δ));
rule RightSubstEq Nil $ϕ Nil $s $t ↪ λ p eq,  (eq $ϕ p);
rule RightSubstEq ($x ⸬ $Γ) $ϕ Nil $s $t ↪ λ p eq x, RightSubstEq $Γ $ϕ Nil $s $t (p x) eq;


//    IFF
//symbol LeftSubstIff Γ ϕ Δ a b : prf (seq ((ϕ a) ⸬ Γ) Δ) → prf (seq ((Iff a b) ⸬ (ϕ b) ⸬ Γ) Δ);
rule LeftSubstIff Nil $ϕ Nil $f $g ↪ λ p iff phit,  p ((symPropEq $f $g (PropExt $f $g iff)) $ϕ phit);
rule LeftSubstIff ($x ⸬ $Γ) $ϕ Nil $s $t ↪ λ p eq phi x, LeftSubstIff $Γ $ϕ Nil $s $t (λ a, p a x) eq phi;

//symbol RightSubstIff Γ ϕ Δ a b : prf (seq Γ ((ϕ a) ⸬ Δ)) → prf (seq ((Iff a b) ⸬ Γ)  ((ϕ b) ⸬ Δ));
rule RightSubstIff Nil $ϕ Nil $f $g ↪ λ p iff,  ((PropExt $f $g iff) $ϕ p);
rule RightSubstIff ($x ⸬ $Γ) $ϕ Nil $f $g ↪ λ p eq x, RightSubstIff $Γ $ϕ Nil $f $g (p x) eq;
