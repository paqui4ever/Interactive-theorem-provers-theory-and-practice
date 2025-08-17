

Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* ~ is infix notation for ~homot~, the type of homotopies between two functions.*)

(* Remember that you can write e.g. ~Locate "~".~ to find information about notation and ~Print negb.~ or ~About negb.~ to find information about a predefined term. *)

Print negb.

Theorem neg_neg_bool: negb ∘ negb ~ idfun bool.
Proof.
  intro n.
  simpl.
  induction n.
    - simpl.
      apply idpath.
    - simpl.
      apply idpath.
Defined.

(* Exercise 2 *)

(* Homotopy is transitive. *)

Theorem concat_htpy {A : UU} {B : A → UU} {f g h : ∏ (x : A) , B x} : (f ~ g) → (g ~ h) → (f ~ h).
Proof.
    intro t.
    intro l.
    intro k.
    exact ((t k) @ (l k)).
Defined.

Infix "~@~" := concat_htpy (at level 70, no associativity).

(* This defines infix notation for concatenation. The stuff in parentheses is not important, but tells Coq the order of operations when it is used in combination with other infix notation.*)

(* Exercise 3 *)

(* Homotopy is associative. *)

(* Hint: use pathsinv0, path_assoc. *)

Theorem assoc_htpy {A : UU} {B : A → UU} {f g h i : ∏ (x : A) , B x} (H : f ~ g) (K : g ~ h) (L : h ~ i) : ((H ~@~ K) ~@~ L) ~ (H ~@~ (K ~@~ L)).
Proof.
    intro x.
    simpl.
    unfold concat_htpy.
    apply pathsinv0.
    apply path_assoc.
Defined.

About pathsinv0.
About path_assoc.

(* Exercise 4 *)

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
  unfold iscontr.
  use tpair.
   - exact tt. (* Th definition of unit is Inductive unit : UU := tt : unit. *) 
   - simpl.
     intro x.
     induction x.
     apply idpath.
Defined.

About unit.
Print iscontr.
About cntr.

(* Exercise 5 *)

Lemma unit_is_prop (x y : unit) : iscontr (x = y).
Proof.
  unfold iscontr.
  use tpair.
    - induction x.
      induction y.
      apply idpath.
    - cbn.
      intro t.
      induction t.
      induction x.
      simpl.
      apply idpath.
Defined.

About unit_rect.
About idpath.
About paths_refl.

(* Exercise 6 *)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    unfold weq in e.
    induction e as [f p].
    intro b.
    unfold isweq in p.
    unfold iscontr in p.
    induction (p b) as [cntr x].
    induction cntr.
    exact (pr1).
Defined.

(* Exercise 7 *)

(* Every contractible type is equivalent to the unit.*)

Lemma contr_to_path {C : UU} {h: iscontr C} {x y : C} : x = y.
Proof.
  induction h as [h1 h2].
  exact (h2 x @ ! (h2 y)). (* x = h1 ~ !(y = h1) is x = h1 ~ h1 = y and because of @ x = y *)
Defined.


Search (∏ C : UU , ∏ x y : C, x = y -> y = x).

Compute idpath tt.

Lemma paths_in_unit (p : tt = tt) : p = idpath tt.
Proof.
    exact (@contr_to_path (tt = tt) (unit_is_prop tt tt) p (idpath tt)).
    (* I pass all the arguments to rocq with ~@~ so the proof works *)
Defined.
  
Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
   unfold weq.
   use tpair.
     - intro c.
       apply unit_iscontr.
     - intro f.
       simpl.
       induction f.
       unfold hfiber.
       induction h as [cntr p].
       use tpair.
         + exact (cntr,,idpath tt).
         + simpl.
           intro t.
           induction t as [q c].
           rewrite (p q).
           rewrite (paths_in_unit c).
           apply idpath. (* Because the parenthesis are: (cntr,, idpath tt) = (cntr,, idpath tt) *)    
Defined.


About weq.
    

(* Exercise 8 *)

(* The type of paths beginning at the same point is always contractible.*)

Theorem contrthm (A : UU) (a : A) : iscontr (∑ x : A, a = x).
Proof.
  use tpair.
    - use tpair.
      exact a.
      simpl.
      apply idpath.
    - simpl.
      intro t.
      induction t as [b x].
      induction x.
      apply idpath.
Defined.
   
