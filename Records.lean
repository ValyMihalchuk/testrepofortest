import SPLean.Theories.XSimp
import SPLean.Theories.XChange
import SPLean.Common.Util
import SPLean.Theories.SepLog
import SPLean.Theories.WP1
import SPLean.Theories.Lang
import SPLean.Theories.Arrays

open Classical


open trm val Theories


abbrev field : Type := ℕ





def hfield (p : loc) (k : field) (v : val) : hProp  :=
  (p + 1 + k) ~~> v

notation:100 p:100 ". " k:100 " ~~> " v:0 => hfield p k v

abbrev hrecord_field: Type := field × val
abbrev hrecord_fields : Type := List hrecord_field


notation "`{" k1 " := " v1 "}" => [(k1, (v1 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "}" => [(k1, (v1 : val)), (k2, (v2 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "; " k3 " := " v3 "}" => [(k1, (v1 : val)), (k2, (v2 : val)), (k3, (v3 : val))]

def hfields (kvs : hrecord_fields) (p:loc): hProp :=
  match kvs with
  | [] => ⌜True⌝
  | (ki, vi) :: kvs' => (p. ki ~~> vi) ∗ (hfields kvs' p)
-- axiom hrecord : hrecord_fields → loc → hProp


--notation p " ~~~> " kvs => hrecord kvs p

--axiom hrecord_not_null : ∀ (p : loc) (kvs : hrecord_fields), hrecord kvs p ==> hrecord kvs p ∗  ⌜p ≠ null⌝

-- Read Operation on Record fields
--axiom val_get_field : field → val



def hfields_lookup (k : field) (kvs : hrecord_fields) : Option val :=
  match kvs with
  | [] => none
  | (ki, vi) :: kvs' => if k = ki then some vi else hfields_lookup k kvs'



def maps_all_fields (n:ℕ) (kvs:hrecord_fields) : Prop :=
  List.map Prod.fst kvs =  List.range' 0 n

def hrecord (kvs:hrecord_fields) (p:loc) : hProp :=
  ∃ʰ (n:ℕ), hheader n p ∗ hfields kvs p ∗ ⌜maps_all_fields n kvs⌝

notation p " ~~~> " kvs => hrecord kvs p

lemma hrecord_elim_aux (kvs:hrecord_fields)
 :
  ∀ (s n:ℕ),
  ((List.map Prod.fst kvs) = List.range' s n  ) →
(List.length kvs) = n :=
by
  induction kvs with
  | nil =>
    intro a b H
    simp at H
    symm at H
    simp[List.range'_eq_nil] at H
    aesop
  | cons x xs Ih =>
    intro s n H
    simp at H
    cases n with
    | zero =>
      have hh : List.range' s 0 = List.nil := by simp[List.range'_eq_nil]
      rw[hh] at H
      simp at H
    | succ n' =>
     rw[←List.range'_append] at H
     simp at H
     simp[Ih _ _ (And.right H)]


lemma hrecord_elim : ∀ p kvs,
  hrecord kvs p ==> hheader (List.length kvs) p ∗ hfields kvs p :=
by
  intro p kvs
  unfold hrecord
  xpull
  intros z Hz
  xsimp
  apply himpl_of_eq
  unfold maps_all_fields at Hz
  simp[hrecord_elim_aux kvs 0 z Hz]



def head : field := 0
def tail : field := 1

open trm prim


def val_get_field  (k: field): val :=
 [lang|
 fun p =>
    let p1 := p ++ 1 in
    let q := p1 ++ ⟨Int.ofNat k⟩ in
    !q]


--notation t1 ". " k => (val_get_field k) t1

lemma triple_get_field : ∀ (p:loc) (k: field) v,
  triple [lang| ⟨val_get_field k⟩ p]
    (p. k ~~> v)
    (fun r => ⌜r = v⌝  ∗ (p. k ~~> v))
:=
by
    xwp
    unfold hfield
    xapp triple_ptr_add_nonneg
    xwp
    xapp triple_ptr_add_nonneg
    sby xapp




/-
lemma demo_hrecord_intro_elim : ∀ p x q,
      (p ~~~> `{ head := x ; tail := q }) ==> ⌜True⌝ :=
by
 intro p x y
 xchange hrecord_elim
 sorry

axiom triple_get_field_hrecord : ∀ (kvs : hrecord_fields) (p : loc) (k : field) (v : val),
  hfields_lookup k kvs = some v →
  triple (trm_app (val_get_field k) p) (hrecord kvs p) (fun r =>  ⌜r = v⌝ ∗ hrecord kvs p)

-- Write Operation on Record fields
axiom val_set_field : field→ val → val
notation t1 ". " k " := " t2 => val_set_field k t1 t2

def hfields_update (k : field) (v : val) (kvs : hrecord_fields) : Option hrecord_fields :=
  match kvs with
  | [] => none
  | (ki, vi) :: kvs' =>
    if k = ki then
      some ((k, v) :: kvs')
    else
      match hfields_update k v kvs' with
      | none => none
      | some kvs'' => some ((ki, vi) :: kvs'')


axiom triple_set_field_hrecord : ∀ (kvs kvs' : hrecord_fields) (k : field) (p : loc) (v : val),
  hfields_update k v kvs = some kvs' →
  triple (trm_app (val_set_field k p) v) (hrecord kvs p) (fun _ => hrecord kvs' p)

-- Allocation of Records
axiom val_alloc_hrecord : List field → trm

axiom triple_alloc_hrecord : ∀ (ks : List field),
  ks = List.range (List.length ks) →
  triple (val_alloc_hrecord ks) emp (funloc p ↦ hrecord (List.map (fun k => (k,val_uninit)) ks) p)

axiom val_new_hrecord_2 : field→ field→ val → val → val
notation "`{" k1 " := " v1 "; " k2 " := " v2 "}" => val_new_hrecord_2 k1 k2 v1 v2

axiom triple_new_hrecord_2 : ∀ (k1 k2 : field) (v1 v2 : val),
  k1 = 0 →
  k2 = 1 →
  triple (`{ k1 := v1; k2 := v2 }) emp (funloc p ↦ p ~~~> `{ k1 := v1; k2 := v2 })

axiom val_new_hrecord_3 : field→ field→ field→ val → val → val → val
notation "`{" k1 " := " v1 "; " k2 " := " v2 "; " k3 " := " v3 "}" => val_new_hrecord_3 k1 k2 k3 v1 v2 v3

axiom triple_new_hrecord_3 : ∀ (k1 k2 k3 : field) (v1 v2 v3 : val),
  k1 = 0 →
  k2 = 1 →
  k3 = 2 →
  triple (`{ k1 := v1; k2 := v2; k3 := v3 }) emp (funloc p ↦  p ~~~> `{ k1 := v1; k2 := v2; k3 := v3 })

-- Deallocation of Records
axiom val_dealloc_hrecord : val
--notation "delete" => trm.val val_dealloc_hrecord

axiom triple_dealloc_hrecord : ∀ (kvs : hrecord_fields) (p : loc),
  triple (trm_app val_dealloc_hrecord p) (hrecord kvs p) (fun _ => emp)

def jj (k : field) (kvs : hrecord_fields) (p:loc) (Q :  val → hProp): hProp :=
match hfields_lookup k kvs with
     | none =>  ⌜False⌝
     | some v => (qwand (fun r => ⌜r = v⌝  ∗ hrecord kvs p) (protect Q))

--axiom xapp_get_field_lemma : ∀ H k p Q,
--  H ==> ∃ʰ kvs, (hrecord kvs p) ∗ (jj k kvs p Q) →
--  H ==> wpgen_app (trm_app (val_get_field k) p) Q


axiom xapp_set_field_lemma : ∀ H k p v Q,
  (H ==> ∃ʰ kvs, (hrecord kvs p) ∗
     match hfields_update k v kvs with
     | none =>  ⌜False⌝
     | some kvs' => qwand (fun _ => hrecord kvs' p) (protect Q) )→
  H ==> wpgen_app (trm_app (val_set_field k p) v) Q
-/
