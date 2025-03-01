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

abbrev HRecordfield: Type := field × val
abbrev HRecordfields : Type := List HRecordfield


notation "`{" k1 " := " v1 "}" => [(k1, (v1 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "}" => [(k1, (v1 : val)), (k2, (v2 : val))]
notation "`{" k1 " := " v1 "; " k2 " := " v2 "; " k3 " := " v3 "}" => [(k1, (v1 : val)), (k2, (v2 : val)), (k3, (v3 : val))]


axiom hrecord : HRecordfields → loc → hProp
notation p " ~~~> " kvs => hrecord kvs p

axiom hrecord_not_null : ∀ (p : loc) (kvs : HRecordfields), hrecord kvs p ==> hrecord kvs p ∗  ⌜p ≠ null⌝

-- Read Operation on Record fields
axiom val_get_field : field → val
notation t1 ". " k => val_get_field k t1

def hfields_lookup (k : field) (kvs : HRecordfields) : Option val :=
  match kvs with
  | [] => none
  | (ki, vi) :: kvs' => if k = ki then some vi else hfields_lookup k kvs'

axiom triple_get_field_hrecord : ∀ (kvs : HRecordfields) (p : loc) (k : field) (v : val),
  hfields_lookup k kvs = some v →
  triple (trm_app (val_get_field k) p) (hrecord kvs p) (fun r =>  ⌜r = v⌝ ∗ hrecord kvs p)

-- Write Operation on Record fields
axiom val_set_field : field→ val → val
notation t1 ". " k " := " t2 => val_set_field k t1 t2

def hfields_update (k : field) (v : val) (kvs : HRecordfields) : Option HRecordfields :=
  match kvs with
  | [] => none
  | (ki, vi) :: kvs' =>
    if k = ki then
      some ((k, v) :: kvs')
    else
      match hfields_update k v kvs' with
      | none => none
      | some kvs'' => some ((ki, vi) :: kvs'')


axiom triple_set_field_hrecord : ∀ (kvs kvs' : HRecordfields) (k : field) (p : loc) (v : val),
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

axiom triple_dealloc_hrecord : ∀ (kvs : HRecordfields) (p : loc),
  triple (trm_app val_dealloc_hrecord p) (hrecord kvs p) (fun _ => emp)

def jj (k : field) (kvs : HRecordfields) (p:loc) (Q :  val → hProp): hProp :=
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
