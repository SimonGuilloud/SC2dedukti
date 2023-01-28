constant symbol Set : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : Set → TYPE; // `t or \tau

constant symbol List:Π a:Set, TYPE;
constant symbol Nil [a] : List a;
constant symbol ⸬   [a] : τ a → List a → List a;

notation ⸬ infix right 20;

symbol append [a] : List a → List a → List a;

rule append Nil $l ↪ $l;
rule append ($x ⸬ $l) $l2 ↪ $x ⸬ (append $l $l2);


constant symbol Nat : TYPE;

constant symbol O : Nat ;
constant symbol S  : Nat → Nat;


builtin "0"  ≔ O;
builtin "+1" ≔ S;

constant symbol nat : Set;

rule τ nat ↪ Nat;


constant symbol Formula : TYPE;
constant symbol formula : Set;
rule τ formula ↪ Formula;

constant symbol Term : TYPE;
constant symbol term : Set;
rule τ term ↪ Term;

constant symbol Id: TYPE;
constant symbol 0:Id;



/*
constant symbol S: Id → Id;

symbol x ≔ 0;
symbol y ≔ S 0;
symbol z ≔ S (S 0);

constant symbol V : Id → Formula;
*/

constant symbol Equality : Term → Term → Formula;

constant symbol Top : Formula;
constant symbol Bot : Formula;

symbol Neg : Formula → Formula;
symbol Implies : Formula → Formula → Formula;
symbol Iff : Formula → Formula → Formula;
symbol And : List formula → Formula;
symbol Or  : List formula → Formula;

symbol HOLE : Formula ;

// x ∨ ¬ x
symbol toto ≔ λ x : Formula, Or ( x ⸬ (Neg x)  ⸬ Nil);

compute toto HOLE;


// symbol form2sequent :
// rule  And Nil ↪ seq Nil;

constant symbol Forall : (Term → Formula) → Formula;
constant symbol Exists : (Term → Formula) → Formula;
symbol ExistsOne : (Term → Formula) → Formula;

constant symbol Sequent : TYPE;
constant symbol seq : List formula → List formula → Sequent;
//type Implies (V x) (Or (V x) (And (V y) (V z)));

symbol myfirst-sequent ≔ λ x : Formula,  λ y : Formula, seq  ((Neg x) ⸬ Nil) (y ⸬ Nil) ;

constant symbol prf : Sequent → TYPE;

symbol insert [a] : τ a → List a → Nat → List a;
rule insert $x ($y ⸬ $l) O ↪ $x ⸬ $l;
rule insert $x Nil O ↪ $x ⸬ Nil;
rule insert $x Nil (S $z) ↪ $x ⸬ (insert $x Nil $z); 
rule insert $x ($y ⸬ $l) (S $z) ↪ $y ⸬ (insert $x $l $z);

symbol swap-multi [a] : List nat → List a → List a → List a;
rule swap-multi Nil Nil $acc ↪ $acc;
rule swap-multi ($i ⸬ $il) ($v ⸬ $vl) $acc ↪ swap-multi $il $vl (insert $v $acc $i) ;

compute swap-multi (3 ⸬ 0 ⸬ 2 ⸬ 1 ⸬ 4 ⸬ Nil) (42 ⸬ 50 ⸬ 167 ⸬ 21 ⸬ 17 ⸬ Nil) Nil;


// Deduction Rules
constant symbol Hypothesis ϕ Γ Δ : prf (seq (ϕ ⸬ Γ) (ϕ ⸬ Δ));
constant symbol SwapLeft Γ Δ (perm: (List nat)) : prf (seq Γ Δ) → prf (seq (swap-multi perm Γ Nil) Δ);
constant symbol SwapRight Γ Δ (perm: (List nat)) : prf (seq Γ Δ) → prf (seq Γ (swap-multi perm Δ Nil));
constant symbol Cut Γ Σ Δ Ω ϕ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ϕ ⸬ Σ) Ω) → prf (seq (append Γ Σ) (append Δ Ω));

constant symbol LeftAnd Γ l Δ : prf (seq (append l Γ) Δ) → prf (seq ((And l) ⸬ Γ) Δ);
// constant symbol LeftOr Γ Σ Δ Ω ϕ ψ : prf (seq (ϕ ⸬ Γ) Δ) → prf (seq  (ψ ⸬ Σ) Ω) → prf (seq ((Or l) ⸬ (append Γ Σ)) (append Δ Ω));
constant symbol LeftImplies Γ Σ Δ Ω ϕ ψ :  prf (seq Γ (ϕ ⸬ Δ)) → prf (seq (ψ ⸬ Σ) Ω) → prf (seq ((Implies ϕ ψ) ⸬ (append Γ Σ)) (append Δ Ω));
constant symbol LeftIff Γ ϕ ψ Δ : prf (seq ((Implies ϕ ψ) ⸬ (Implies ψ ϕ) ⸬ Γ) Δ) → prf (seq ((Iff ϕ ψ) ⸬ Γ) Δ);
constant symbol LeftNot Γ ϕ Δ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq ( (Neg ϕ) ⸬ Γ) Δ);
constant symbol LeftForall Γ ϕ t Δ : prf (seq ((ϕ t) ⸬ Γ) Δ) → prf (seq ((Forall ϕ) ⸬ Γ) Δ);
constant symbol LeftExists Γ ϕ Δ : (Π x:Term, prf (seq ((ϕ x) ⸬ Γ) Δ)) → prf (seq ((Exists ϕ) ⸬ Γ) Δ);
constant symbol LeftExistsOne Γ ϕ Δ : prf (seq ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Γ) Δ) → 
                                      prf (seq ((ExistsOne ϕ ⸬ Γ)) Δ);

// constant symbol RightAnd Γ ϕ Σ : prf (seq Γ (ϕ ⸬ Δ)) → prf (seq  Σ (ψ ⸬ Ω)) → prf (seq (append Γ Σ) ((And l) ⸬ (append Δ Ω)));
constant symbol RightOr Γ l Δ : prf (seq Γ (append l Δ)) → prf (seq Γ ((Or l) ⸬ Δ));
constant symbol RightImplies Γ ϕ ψ Δ : prf (seq (ϕ ⸬ Γ) (ψ ⸬ Δ)) → prf (seq Γ ((Implies ϕ ψ) ⸬ Δ));
constant symbol RightIff Γ Σ Δ Ω ϕ ψ : prf (seq Γ ((Implies ϕ ψ) ⸬ Δ)) → prf (seq  Σ ((Implies ψ ϕ) ⸬ Ω)) → prf (seq (append Γ Σ) ((Iff ϕ ψ) ⸬ (append Δ Ω)));
constant symbol RightNot Γ ϕ Δ : prf (seq Γ Δ) → prf (seq  Γ ((Neg ϕ) ⸬ Δ));
constant symbol RightForall Γ ϕ Δ : (Π x:Term, prf (seq Γ ((ϕ x) ⸬ Δ))) → prf (seq Γ ((Forall ϕ) ⸬ Δ));
constant symbol RightExists Γ ϕ t Δ : prf (seq Γ ((ϕ t) ⸬ Δ) ) → prf (seq Γ ((Exists ϕ) ⸬ Δ));
constant symbol RightExistsOne Γ ϕ Δ : prf (seq Γ ((Exists (λ y : Term, (Forall (λ x : Term, (Iff (Equality x y) (ϕ x)))))) ⸬ Δ)) → 
                                      prf (seq Γ ((ExistsOne ϕ) ⸬ Δ));

constant symbol LeftWeakening Σ Γ Δ : prf (seq Γ Δ) → prf (seq (append Σ Γ) Δ);
constant symbol RightWeakening Γ Ω Δ : prf (seq Γ Δ) → prf (seq Γ (append Ω Δ));

constant symbol LeftRefl Γ t Δ : prf (seq ((Equality t t) ⸬ Γ) Δ) → prf (seq Γ Δ);
constant symbol RightRefl t : prf (seq Nil ((Equality t t) ⸬ Nil));


symbol Inst (Γ Δ : List formula) (ϕ ψ : Term → Formula) t : (Π (x : Term), prf (seq ((ϕ x) ⸬ Γ) ((ψ x) ⸬ ))) → prf (seq ((ϕ t) ⸬ Nil) ((ψ t) ⸬ Nil)) ;
// ≔ λ x, prf (seq (ϕ x) (ψ x)) → prf (seq (ϕ t) (ψ t)) ;

// Builtin
// Syntactic sugar - And, Iff, Implies, ExistsOne

symbol map [a] [b] : (τ a → τ b) → List a → List b ;
rule map _ Nil ↪ Nil;
rule map $f ($x ⸬ $l) ↪ ($f $x) ⸬ (map $f $l);

rule And $l ↪ Neg (Or (map Neg $l));
rule Iff $ϕ $ψ ↪ And ((Implies $ϕ $ψ) ⸬ (Implies $ψ $ϕ) ⸬ Nil);
rule Implies $ϕ $ψ ↪ Or ((Neg $ϕ) ⸬ $ψ ⸬ Nil) ;
rule ExistsOne $f ↪ Forall (λ y, (Exists (λ x, Iff (Equality x y) ($f x))));

// Rewriting rules

rule Or Nil ↪ Top;

// A1 - Commutativité

// A2 - Associativité

symbol norm : Formula → Formula;
symbol flatten : List formula → List formula ;
rule flatten Nil ↪ Nil;
rule flatten ((Or $l1) ⸬ $l2) ↪ append (flatten $l1) (flatten $l2);
rule flatten ((Neg $x) ⸬ $l) ↪ (Neg (norm $x)) ⸬ (flatten $l);
rule flatten (Bot ⸬ $l) ↪ Bot ⸬ (flatten $l);
rule flatten (Top ⸬ $l) ↪ Bot ⸬ (flatten $l);

// rule norm (Or ((Or $l1) ⸬ $l2)) ↪ Or (append (norm $l1) (norm $l2));
// rule Or ((Or $l1) ⸬ $l2) ↪ Or (append $l1 $l2);

rule norm (Or ((Or $l1) ⸬ $l2)) ↪ Or (append (flatten $l1) (flatten $l2)) ;

compute norm (Or (Or (Top ⸬ Nil) ⸬ Bot ⸬ (Or (Bot ⸬ Nil)) ⸬ Nil));

rule Or ($x ⸬ Nil) ↪ $x;

// A3 -
// rule Or

// A4 -
// rule

// A5

rule Neg (Neg $x) ↪ $x;

rule Neg Bot ↪ Top;
rule Neg Top ↪ Bot;
