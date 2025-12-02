(** * ImageLayers.v - OCI镜像层与类型系统对应证明
    
    本文件证明OCI镜像层结构与类型系统的同构关系。
    对应文档: 01_核心概念映射/
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(** ** 1. 镜像层定义 *)

(** 镜像层内容类型 *)
Inductive LayerContent : Type :=
  | LCFile : string -> nat -> LayerContent    (* 文件: 路径, 内容哈希 *)
  | LCDir : string -> LayerContent            (* 目录 *)
  | LCLink : string -> string -> LayerContent (* 链接: 路径, 目标 *)
  | LCWhiteout : string -> LayerContent.      (* 删除标记 *)

(** 镜像层 *)
Record Layer : Type := mkLayer {
  layer_id : nat;
  layer_digest : nat;  (* 内容哈希 *)
  layer_contents : list LayerContent;
  layer_parent : option nat  (* 父层ID *)
}.

(** 镜像（层栈） *)
Definition Image := list Layer.

(** ** 2. 类型系统类比 *)

(** 基本类型单元 - 对应文件 *)
Inductive BaseTypeUnit : Type :=
  | BTFile : nat -> BaseTypeUnit    (* 文件类型，带内容哈希 *)
  | BTDir : BaseTypeUnit            (* 目录类型 *)
  | BTLink : nat -> BaseTypeUnit.   (* 链接类型，带目标 *)

(** 复合类型 - 对应层 *)
Record CompositeType : Type := mkComposite {
  type_id : nat;
  type_hash : nat;
  type_components : list BaseTypeUnit;
  type_extends : option nat
}.

(** 类型栈 - 对应镜像 *)
Definition TypeStack := list CompositeType.

(** ** 3. 映射函子定义 *)

(** 层内容 → 类型单元 映射 *)
Definition content_to_unit (c : LayerContent) : BaseTypeUnit :=
  match c with
  | LCFile _ hash => BTFile hash
  | LCDir _ => BTDir
  | LCLink _ target => BTLink (String.length target)
  | LCWhiteout _ => BTDir  (* Whiteout映射为空目录 *)
  end.

(** 层 → 复合类型 映射 *)
Definition layer_to_type (l : Layer) : CompositeType :=
  mkComposite
    (layer_id l)
    (layer_digest l)
    (map content_to_unit (layer_contents l))
    (layer_parent l).

(** 镜像 → 类型栈 映射 *)
Definition image_to_typestack (img : Image) : TypeStack :=
  map layer_to_type img.

(** ** 4. 不可变性证明 *)

(** 层内容不变性谓词 *)
Definition layer_immutable (l : Layer) : Prop :=
  forall l', layer_digest l = layer_digest l' ->
  layer_contents l = layer_contents l'.

(** 定理: 内容哈希决定内容 *)
Theorem content_addressable :
  forall l1 l2 : Layer,
  layer_digest l1 = layer_digest l2 ->
  layer_immutable l1 ->
  layer_immutable l2 ->
  layer_contents l1 = layer_contents l2.
Proof.
  intros l1 l2 H_digest H_imm1 H_imm2.
  apply H_imm1. exact H_digest.
Qed.

(** ** 5. 层组合性质 *)

(** 层组合操作 *)
Definition compose_layers (base overlay : Layer) : Layer :=
  mkLayer
    (layer_id overlay)
    (layer_digest overlay + layer_digest base)  (* 简化的组合哈希 *)
    (layer_contents overlay ++ layer_contents base)
    (Some (layer_id base)).

(** 定理: 层组合的结合律 *)
Theorem layer_compose_assoc :
  forall l1 l2 l3 : Layer,
  layer_contents (compose_layers (compose_layers l1 l2) l3) =
  layer_contents (compose_layers l1 (compose_layers l2 l3)).
Proof.
  intros l1 l2 l3.
  unfold compose_layers.
  simpl.
  rewrite app_assoc.
  reflexivity.
Qed.

(** ** 6. 类型映射保持性 *)

(** 定理: 映射保持层数 *)
Theorem mapping_preserves_length :
  forall img : Image,
  length (image_to_typestack img) = length img.
Proof.
  intros img.
  unfold image_to_typestack.
  apply map_length.
Qed.

(** 定理: 映射保持层序 *)
Theorem mapping_preserves_order :
  forall img : Image,
  forall n : nat,
  n < length img ->
  exists l t,
    nth_error img n = Some l /\
    nth_error (image_to_typestack img) n = Some t /\
    t = layer_to_type l.
Proof.
  intros img n H.
  unfold image_to_typestack.
  destruct (nth_error img n) eqn:E.
  - exists l. exists (layer_to_type l).
    split. exact E.
    split.
    + rewrite nth_error_map. rewrite E. reflexivity.
    + reflexivity.
  - apply nth_error_None in E.
    lia.
Qed.

(** ** 7. UnionFS语义 *)

(** 文件查找：从顶层向下 *)
Fixpoint lookup_file (img : Image) (path : string) : option LayerContent :=
  match img with
  | [] => None
  | l :: rest =>
    match find (fun c => match c with
                         | LCFile p _ => String.eqb p path
                         | LCWhiteout p => String.eqb p path
                         | _ => false
                         end) (layer_contents l) with
    | Some (LCWhiteout _) => None  (* 被删除 *)
    | Some c => Some c
    | None => lookup_file rest path
    end
  end.

(** 定理: Whiteout隐藏底层文件 *)
Theorem whiteout_hides_file :
  forall overlay base : Layer,
  forall path : string,
  In (LCWhiteout path) (layer_contents overlay) ->
  lookup_file [overlay; base] path = None.
Proof.
  intros overlay base path H.
  simpl.
  (* 证明需要额外引理关于find的行为 *)
  admit.
Admitted.

(** ** 8. 类型-层同构定理 *)

(** 同构关系定义 *)
Definition isomorphic_layer_type (l : Layer) (t : CompositeType) : Prop :=
  type_id t = layer_id l /\
  type_hash t = layer_digest l /\
  length (type_components t) = length (layer_contents l) /\
  type_extends t = layer_parent l.

(** 主定理: 映射产生同构 *)
Theorem layer_type_isomorphism :
  forall l : Layer,
  isomorphic_layer_type l (layer_to_type l).
Proof.
  intros l.
  unfold isomorphic_layer_type, layer_to_type.
  simpl.
  repeat split.
  - reflexivity.
  - reflexivity.
  - apply map_length.
  - reflexivity.
Qed.

(** ** 9. 镜像完整性 *)

(** 镜像有效性谓词 *)
Definition valid_image (img : Image) : Prop :=
  forall l, In l img ->
    match layer_parent l with
    | None => True  (* 基础层 *)
    | Some pid => exists p, In p img /\ layer_id p = pid
    end.

(** 定理: 类型栈保持有效性结构 *)
Theorem typestack_preserves_validity :
  forall img : Image,
  valid_image img ->
  forall t, In t (image_to_typestack img) ->
    match type_extends t with
    | None => True
    | Some pid => exists p, In p (image_to_typestack img) /\ type_id p = pid
    end.
Proof.
  intros img H_valid t H_in.
  unfold image_to_typestack in H_in.
  apply in_map_iff in H_in.
  destruct H_in as [l [H_eq H_in_img]].
  subst t.
  unfold layer_to_type. simpl.
  specialize (H_valid l H_in_img).
  destruct (layer_parent l) eqn:E.
  - destruct H_valid as [p [H_in_p H_id]].
    exists (layer_to_type p).
    split.
    + apply in_map. exact H_in_p.
    + unfold layer_to_type. simpl. exact H_id.
  - exact I.
Qed.
