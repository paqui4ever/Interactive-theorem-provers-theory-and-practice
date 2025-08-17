Unset Universe Checking.
Require Export UniMath.Foundations.All.

(* Instructions: there are 10 exercises. Succesfully completing x exercises will earn you a grade of x. (No partial credit will be given.) Please alter the following comment to tell me which exercises you completed below.*)

(* I completed 3 exercises: Exercise 1, 2, 3, 4, 5, 6, 7, 8, 9, 10.*)

(* Exercise 1 *)

Theorem comp_app { P Q R : UU } (f : P → Q) (g : Q → R) (p : P) : R.
Proof.
  exact (g (f p)).
Defined.
  

(* Exercise 2 *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
(* Another way to combine paths. *)
Proof.
  induction p.
  induction q.
  apply idpath.
Defined.

(* Exercise 3 *)

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
(* Check that the above way of combining paths does the `right thing'. *)
Proof.
  induction p.
  unfold path_combination.
  simpl.
  apply idpath.
Defined.

(* Exercise 4 *)

Theorem exp : nat → nat → nat.
Proof.
  intro n.
  intro m.
  induction m.
    - exact 1.
    - exact (n * IHm).
Defined.

Compute (exp 5 1).

Compute (exp 7 0).

Compute (exp 0 7).

Compute (exp 3 2).

(* Exercise 5 *)

Theorem curried_proj {P Q R : UU} : (P → (Q × R)) → (P → Q).
Proof.
  intro f.
  intro p2.
  induction f as [p qr].
    - exact p.
    - exact p2.
Defined.
  

(* Exercise 6 *)

Search (∏ X Y : UU, ∏ f : X → Y, ∏ x y : X, x = y → (f x) = (f y)).
Print maponpaths.

(* This command searches the library for functions of this kind. You should see in the output that ~maponpaths~ is of this kind. You can then print ~maponpaths~ (i.e. write "Print maponpaths.") to see the definition.

You can use this to find other lemmas from the library. You can use any facts without proof from the library about addition and multiplication as well as ~maponpaths~.*)

Search (∏ X : UU, ∏ x y : X, x = y -> y = x).
Search (∏ n : nat, n * 1 = n).
Search (∏ n : nat, n + 0 = n).
Search (∏ n : nat, n * 0 = 0).
Search (∏ n m : nat, n*m = m*n).
Search (∏ n m, m + (S n) = S (m + n)).

Lemma succ_prop {n m : nat} : n + S m = S (n + m).
Proof.
  induction n.
    - simpl.
      apply idpath.
    - simpl.
      apply maponpaths.
      exact IHn.
Defined.
  
About add.
About natmultcomm.

Theorem exp_hom {l m n : nat} : exp l (m + n) = (exp l m) * (exp l n).
(* `exp l` takes addition to multiplication.*)
Proof.
  induction n.
    - simpl.
      rewrite (natmultr1).
      rewrite (natplusr0).
      apply idpath.
    - simpl.
      rewrite succ_prop.
      simpl.
      rewrite IHn.
      apply pathsinv0.
      rewrite natmultcomm.
      rewrite natmultassoc.
      rewrite <- (natmultcomm (exp l n) (exp l m)).
      apply idpath.
Defined.
      
      
(* Exercise 7 *)

(* isaprop is defined differently in UniMath than we defined in lectures. Show that these two definitions are the the same. *)

(* Note that this is the hardest exercise, but the ones following depend on it. Feel free to leave it admitted and use the result without proof in the following exercises. *)

Lemma contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
    unfold isaprop.
    simpl.
    intros x y.
    unfold iscontr.
    use tpair.
    induction h as [cntr p].
    + exact (path_combination (p x) (p y)).
    + simpl.
      intro t.
      induction t.
      exact (path_combination_fact (pr2 h x)).
Defined.

Theorem prop_thm {P : UU} : isaprop P <-> (∏ x y : P, x = y).
(* The different definitions of isaprop are logically equivalent. *)
Proof.
  split.
    - intros p x y.
      induction (p x y) as [f _].
      exact f.
    - intro f.
      unfold isaprop.
      simpl.
      intros x x'.
      apply contr_is_prop.
      unfold iscontr.
      use tpair.
        + exact x.
        + simpl.
          intro t.
          exact (f t x).
Defined.

(* Exercise 8 *)

(* Show that the dependent product type former commutes with `isaprop`.*)

About funextsec.

Theorem prop_commutes_Π {A : UU} {B : A → UU} (p : ∏ x : A, isaprop (B x)) : isaprop (∏ x : A, (B x)).
Proof.
  intros f g.
  unfold isaprop.
  unfold isofhlevel.
  apply contr_is_prop.
  unfold iscontr.
  use tpair.
    - exact f.
    - simpl.
      intro t.
      apply funextsec.
      intro x.
      apply p.
Defined.

(* Exercise 9 *)

(* Show that isweq f is a proposition. *)

(* Use ~isapropisofhlevel~ from the library. *)

About isapropisofhlevel.
About isweq.

Lemma hlevelcontr : iscontr = isofhlevel 0.
Proof.
  apply idpath.
Defined.
  
Theorem isweq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
  unfold isweq.
  apply prop_commutes_Π.
  intro x.
  rewrite hlevelcontr.
  apply (isapropisofhlevel 0).
Defined.  

(* Exercise 10 *)

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

(* You are allowed to use isweq_iso from the library in this proof: it says if f is a quasiequivalence, then f is an equivalence in that sense.*)

About isweq_iso.

Theorem prop_equiv_to_log_equiv (P Q : hProp) : (P ≃ Q) <-> (P <-> Q).
(* An equivalence between propositions is (logically equivalent to) a logical equivalence. *)
Proof.
  split.
    - intro pq.
      split.
        + intro p.
          exact (pq p).
        + intro q.
          exact (inverse pq q).
    - intro pq.
      induction pq as [f g].
      unfold weq.
      use tpair.
        + exact f.
        + simpl.
          apply (isweq_iso f g).
          intro x.
          apply prop_thm.
          unfold isaprop.
          unfold isofhlevel.
          intros n m.
          unfold iscontr.
          use tpair.
          apply (pr2 P).
          simpl.
          intro t.
          set (h := pr1 (pr2 P n m)).
          apply (pr2 P).
          intro y.
          apply prop_thm.
          unfold isaprop.
          unfold isofhlevel.
          intros n m.
          unfold iscontr.
          use tpair.
          apply (pr2 Q).
          simpl.
          intro t.
          set (h := pr1 (pr2 Q n m)).
          apply (pr2 Q).
Defined.
          
          
          
          
    
       
