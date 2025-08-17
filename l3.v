Require Export UniMath.Foundations.All.

(* Example 1*)

(* Notes:
- idpath is the name in Unimath for refl.
- Defined as maponpaths in UniMath.Foundations.PartA.*)

(*
The identity type is defined in Unimath as:

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .
*)

Definition ap {A B : UU} (f : A → B) {x y : A} (p : x = y) : f x = f y.
Proof.
  induction p.
  apply idpath.
Defined.

Search (∏ A B : UU , ∏ f : A → B, ∏ x y : A , x = y → f x = f y).

About maponpaths.

About ap.

(* Example 2 *)

Print add.

Definition left_unit (n : nat) : add 0 n = n.
Proof.
  simpl.
  apply idpath.
Defined.

Definition right_unit (n : nat) : add n 0 = n.
Proof.
  induction n.
  - apply idpath.
  - cbn. (* call-by-name, it applies the definition for making it easier visually *)
    apply ap. (* It strips off the S which would be the f in the context of ap *) 
    exact IHn.
Defined.

Definition right_unit_again (n : nat) : add n 0 = n.
Proof.
  induction n.
  - apply idpath.
  - cbn.
    (* set (myeq := ap S IHn). *) 
    rewrite IHn.
    apply idpath.
Defined.

(* Example 3 *)

Definition reflexive {A : UU} (R: A → A → UU) : UU := ∏ a : A, R a a.

(* We can make the parameter {A:UU} in paths explicit by writing @paths. *)

Lemma reflexive_paths (A : UU): reflexive (@paths A).
Proof.
  unfold reflexive. (* simpl and cbn doesn't work, so I have to use unfold *)
  intro a.
  apply idpath.
Defined.

(* Example 4 *)

Definition symmetric {A : UU} (R: A → A → UU) : UU := ∏ (a b : A), R a b → R b a.

Lemma symmetric_paths (A : UU) : symmetric (@paths A).
Proof.
  unfold symmetric.
  intros a b.
  intro p.
  induction p.
  apply idpath.
Defined.

(* Example 5 *)

Definition transitive {A : UU} (R: A → A → UU) : UU := ∏ (a b c : A), a = b → b = c → a = c.

Lemma transitive_paths (A : UU) : transitive (@paths A).
Proof.
  unfold transitive.
  intros a b c p q.
  induction p.
  induction q.
  apply idpath.
Defined.

(* Example 6 *)

Definition equivalence {A : UU} (R: A → A → UU) : UU := (reflexive R) × (symmetric R) × (transitive R).

Theorem equivalence_paths (A : UU) : equivalence (@paths A).
Proof.
  exact (reflexive_paths A,,symmetric_paths A,,transitive_paths A). (* Using lemmas to prove a bigger thing, theorem in this case *)
Defined.

(* Example 7 *)

(* Everything respects equality. *)

(* Note: transport is defined as transportf in UniMath.Foundations.PartA.*)

Theorem transport {A : UU} {D : A → UU} {a b : A} (d : D a) (p: a = b) : D b.
Proof.
  induction p.
  exact d.
Defined.


(*********************************)

(* Exercise 8 *)

Theorem complicatedTransport {A : UU} {D : A → UU} {a b c : A} (p : a = b) (q : b = c) (d : D c) : D a.
Proof.
  induction q.
  induction p.
  exact d.
Defined.

Theorem complicatedTransportAgain {A : UU} {D : A → UU} {a b c : A} (p : a = b) (q : b = c) (d : D c) : D a.
Proof.
Admitted.

(* Exercise 9 *)

Lemma add_S_comm : ∏ n m : nat , n + S m = S (n + m).
Proof.
  intro n.
  intro m.
  induction n.
    - apply left_unit.
    - cbn.
     apply ap.
     exact (IHn).
Defined.
  
  


Theorem add_comm : ∏ n m : nat , n + m = m + n.
Proof.
  intro n.
  intro m.
  induction n.
    - rewrite right_unit.
      rewrite left_unit.
      apply idpath.
    - cbn.
      rewrite add_S_comm.
      apply ap.
      exact IHn.
Defined.


(* Exercise 9 *)

Theorem mul_left_id : ∏ n : nat , mul 1 n = n.
Proof.
  induction n.
    - simpl.
      apply idpath.
    - simpl.
      apply idpath.
Defined.


(* Exercise 10 *)

Theorem mul_right_id : ∏ n : nat , mul n 1 = n.
Proof.
  induction n.
  - simpl.
    apply idpath.
  - simpl.
    rewrite IHn.
    (* I wanna prove that forall n of type nat n + 1 = S n *)
    apply natpluscomm.
Defined.

About S.
Print add.

(* Exercise 11 *)

(* Define what is means to be divisible by 2 and divisible by 4, and show that being divisible by 4 implies being divisible by 2. *)
Definition zeroMod2 (n: nat) : UU :=  ∑ (m: nat), mul m 2 = n.

Definition zeroMod4 (n: nat) : UU :=  ∑ (m: nat), mul m 4 = n.

Theorem zeroMod2ImpliesZeroMod4: (∏ n : nat , zeroMod4 n -> zeroMod2 n).
Proof.
  intro n.
  intro z4.
  induction n.
    - 
      