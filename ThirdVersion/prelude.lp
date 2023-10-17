constant symbol T0 : TYPE;

// Interpretation of set codes in TYPE

injective symbol τ : T0 → TYPE;

// Definitions of Sets
constant symbol Set: T0 → TYPE;
constant symbol Nil [a] : Set a;
constant symbol Sing [a] : τ a → Set a;
symbol union : Π a:T0, Set a → Set a → Set a;
symbol ⸬  [a] : τ a → Set a → Set a;


notation ⸬ infix right 20;
//idempotence

// Definition of natural numbers

constant symbol Nat : TYPE;

constant symbol O : Nat ;
constant symbol S  : Nat → Nat;


builtin "0"  ≔ O;
builtin "+1" ≔ S;

constant symbol nat : T0;

rule τ nat ↪ Nat;


// Definitions of operations on Sets

symbol append [a] : Set a → Set a → Set a;

rule append Nil       $l  ↪ $l;
rule append ($x ⸬ $l) $l2 ↪ $x ⸬ (append $l $l2);
rule append $Γ Nil ↪ $Γ;

symbol map [a] [b] : (τ a → τ b) → Set a → Set b ;
rule map _ Nil ↪ Nil;
rule map $f ($x ⸬ $l) ↪ ($f $x) ⸬ (map $f $l);

symbol reverse [a] : Set a → Set a → Set a;
rule reverse Nil $acc ↪ $acc;
rule reverse ($x ⸬ $xs) $acc ↪ reverse $xs ($x ⸬ $acc);



//insert an element at a given place in a Set
symbol insert [a] : τ a → Set a → Nat → Set a;
rule insert $x ($y ⸬ $l) O ↪ $x ⸬ $l;
rule insert $x Nil O ↪ $x ⸬ Nil;
rule insert $x Nil (S $z) ↪ $x ⸬ (insert $x Nil $z); 
rule insert $x ($y ⸬ $l) (S $z) ↪ $y ⸬ (insert $x $l $z);

// count elements in a Set and replace them by their index
symbol enumerate [a] :  Nat → Set a → Set nat ;
rule enumerate $n Nil ↪ Nil;
rule enumerate $n ($x ⸬ $l) ↪ $n ⸬ (enumerate (S $n) $l);


symbol swap-multi [a] : Set nat → Set a → Set a → Set a;
rule swap-multi Nil $Γ $acc ↪ append $acc $Γ;
rule swap-multi  ($i ⸬ $il) ($v ⸬ $vl) $acc ↪ swap-multi $il $vl (insert $v $acc $i) ;

//symbol equal-int-Sets : Set nat → Set nat → Nat;
//rule equal-int-Sets Nil Nil ↪ 0;
//rule equal-int-Sets ($x ⸬ $xs) Nil ↪ 1;
//rule equal-int-Sets Nil ($y ⸬ $ys) ↪ 1;
//rule equal-int-Sets (0 ⸬ $xs) (0 ⸬ $ys) ↪ equal-int-Sets $xs $ys;
//rule equal-int-Sets (0 ⸬ $xs) ((S $m) $ys) ↪ 1;
//rule equal-int-Sets  ((S $n) ⸬ xs) (0 $ys) ↪ 1;
//rule equal-int-Sets ((S $n) ⸬ xs) ((S $m) ⸬ ys) ↪ equal-int-Sets ($n ⸬ $xs) ($m ⸬ $ys);

symbol is-natural : Set nat → Nat → Nat;
rule is-natural Nil $n ↪ 0;
rule is-natural ($n ⸬ $xs)  $n ↪ is-natural $xs (S $n);

symbol is-perm : Set nat → Nat;
rule is-perm $l ↪ is-natural (swap-multi $l $l $l) 0;


symbol permute [a] : Set nat → Set a → Set a → Set a;
symbol permute2 [a] : Nat → Set nat → Set a → Set a → Set a;

rule permute $ln $l $acc ↪ permute2 (is-perm $ln) $ln $l $acc;
rule permute2 0 $ln $l $acc ↪ swap-multi $ln $l $acc;



symbol swap [a] : Set a → Nat → Set a;
rule swap Nil            _      ↪ Nil;
rule swap ($x ⸬ Nil)     _      ↪ $x ⸬ Nil;
rule swap ($x ⸬ $y ⸬ $l) 0      ↪ ($y ⸬ $x ⸬ $l);
rule swap ($x ⸬ $y ⸬ $l) (S $n) ↪ ($x ⸬ (swap ($y ⸬ $l) $n));
