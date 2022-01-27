theory nanoCoP3 imports Main
begin

primrec member where
  \<open>member _ [] = False\<close> |
  \<open>member m (n # A) = (m = n \<or> member m A)\<close>

lemma member_iff [iff]: \<open>member m A \<longleftrightarrow> m \<in> set A\<close>
  by (induct A) simp_all

primrec common where
  \<open>common _ [] = False\<close> |
  \<open>common A (m # B) = (member m A \<or> common A B)\<close>

lemma common_iff [iff]: \<open>common A B \<longleftrightarrow> set A \<inter> set B \<noteq> {}\<close>
  by (induct B) simp_all


datatype ('a) clause_elem
  = LitM "bool" 'a
  | Matrix "'a matrix_elem list"
and ('a) matrix_elem
  = LitC "bool" 'a
  | Clause \<open>'a clause_elem list\<close>

fun ext where
  \<open>ext ys [] = True\<close> |
  \<open>ext ys (x # xs) = (member x ys \<and> ext ys xs)\<close>

lemma ext_iff [iff]: \<open>ext ys xs \<longleftrightarrow> (\<forall> x \<in> set xs. x \<in> set ys)\<close>
  by (induct xs) auto

abbreviation \<open>perm xs ys \<equiv> ext xs ys \<and> ext ys xs\<close>

lemma perm_iff [iff]: \<open>perm xs ys \<longleftrightarrow> set xs = set ys\<close>
  by (induct xs) auto

(* ATTEMPT 1
Difference to original calculus:
I am removing the capability for arbitrary switching to 
-clauses that has already been visited
-clauses that are direct horizontal extensions of a path

How do you direct a path inwards in original?
By removing all matrices but 1 using extension
Then choosing a clause from that matrix using decomposition
Then you can pick literal from that clause to your path
And extend to other clauses of that inner matrix

Can this be done in my scheme?
No, after using decomposition the other clauses are destroyed and can no longer be accessed

Fix1
Add active clause that might not be in same state as its parallel in the matrix

Problems with fix:
Will need to reintroduce arbitrary jumps

Fix2
Replace decomposition with another kind of extension
If it can be solved with the elements on the current path
then we can use the path produced by its solving to solve the rest parent matrix

inductive nanoCoP where
  Axiom: \<open>nanoCoP ([] # Mat) Path\<close> |
  PermMat: \<open>perm Mat1 Mat2  \<Longrightarrow> nanoCoP Mat1 Path \<Longrightarrow> nanoCoP Mat2 Path\<close> |
  PermCls: \<open>perm Cls1 Cls2  \<Longrightarrow> nanoCoP (Cls1 # Mat) Path \<Longrightarrow> nanoCoP (Cls2 # Mat) Path\<close> |
  Reduction: \<open>
    pol1 \<longleftrightarrow> \<not>pol2 \<Longrightarrow> member (Lit pol1 prp) Path \<Longrightarrow> nanoCoP (Cls # Mat) Path \<Longrightarrow> 
      nanoCoP ((Lit pol2 prp # Cls) # Mat) Path\<close> |
  Extension: \<open>
    nanoCoP (Cls # Mat) Path \<Longrightarrow> nanoCoP (Cls # Mat) (Lit pol prp # Path) \<Longrightarrow> 
      nanoCoP ((Lit pol prp # Cls) # Mat) Path\<close> |
  Decomposition: \<open>
    member cls mat \<Longrightarrow> nanoCoP ((cls @ Cls) # Mat) Path \<Longrightarrow> 
      nanoCoP ((Matrix mat # Cls) # Mat) Path\<close>
*)

(*ACTIVE CLAUSE NANOCOP - MISSING COHERENT EXTENSION
inductive nanoCoP where
  Axiom: \<open>nanoCoP [] Mat Path\<close> |
  PermCls: \<open>perm Cls1 Cls2  \<Longrightarrow> nanoCoP Cls1  Mat Path \<Longrightarrow> nanoCoP Cls2 Mat Path\<close> |
  Reduction: \<open>
    pol1 \<longleftrightarrow> \<not>pol2 \<Longrightarrow> member (Lit pol1 prp) Path \<Longrightarrow> nanoCoP Cls Mat Path \<Longrightarrow> 
      nanoCoP (Lit pol2 prp # Cls) Mat Path\<close> |
  Extension: \<open>
    nanoCoP Cls Mat (Lit pol prp # Path) \<Longrightarrow> nanoCoP Cls Mat Path \<Longrightarrow> 
      nanoCoP (Lit pol prp # Cls) Mat Path\<close> |
  Decomposition: \<open>
    member cls mat \<Longrightarrow> nanoCoP (cls @ Cls) Mat Path \<Longrightarrow> 
      nanoCoP (Matrix mat # Cls) Mat Path\<close>
*)

(*
I think this works, though it requires much more careful choices than original
Will have to think hard about copy-clauses for FOL*)
inductive nanoCoP where
  Axiom: 
    \<open>nanoCoP (Clause [] # Mat) Path\<close> |
  PermMat: 
    \<open>nanoCoP Mat2 Path\<close> if 
    \<open>perm Mat1 Mat2\<close> and
    \<open>nanoCoP Mat1 Path\<close> |
  PermCls: 
    \<open>nanoCoP (Clause Cls2 # Mat) Path\<close> if 
    \<open>perm Cls1 Cls2\<close> and 
    \<open>nanoCoP (Clause Cls1 # Mat) Path\<close> |
  ReductionLit: 
    \<open>nanoCoP (Clause (LitM pol prp # Cls) # Mat) Path\<close> if
    \<open>member (\<not>pol, prp) Path\<close> and 
    \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ReductionLitC: 
    \<open>nanoCoP (LitC pol prp # Mat) Path\<close> if 
    \<open>member (\<not>pol, prp) Path\<close> |
  ReductionMat: 
    \<open>nanoCoP (Clause (Matrix mat # Cls) # Mat) Path\<close> if
    \<open>nanoCoP mat Path\<close> and
    \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ExtensionLit: 
    \<open>nanoCoP (Clause (LitM pol prp # Cls) # Mat) Path\<close> if
    \<open>nanoCoP Mat ((pol, prp) # Path)\<close> and
    \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ExtensionLitC: 
    \<open>nanoCoP (LitC pol prp # Mat) Path\<close> if
    \<open>nanoCoP Mat ((pol, prp) # Path)\<close> |
  ExtensionMat: 
    \<open>nanoCoP (Clause (Matrix mat # Cls) # Mat) Path\<close> if
    \<open>nanoCoP (Clause [Matrix mat] # Mat) Path\<close> and
    \<open>nanoCoP (Clause Cls # Mat) Path\<close>

(*Example proofs*)
context begin
private datatype props = P | Q | R

(*Way more steps are required than in the original
Part of this is because of the replacement with beta-clauses, which is a permissible rule*)
private lemma \<open>nanoCoP 
  [
    Clause [LitM False P],
    Clause [
      Matrix [Clause [LitM True P],Clause [LitM False Q]],
      Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
    ],
    Clause [LitM True Q]
  ] 
  []\<close>
proof-
  from ExtensionLit have ?thesis if \<open>nanoCoP 
    [
      Clause [
        Matrix [Clause [LitM True P],Clause [LitM False Q]],
        Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
      ],
      Clause [LitM True Q]
    ] 
  [(False, P)]\<close> and \<open>nanoCoP 
    [
      Clause [],
      Clause [
        Matrix [Clause [LitM True P],Clause [LitM False Q]],
        Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
      ],
      Clause [LitM True Q]
    ] 
  []\<close> using that by fast
  with Axiom have ?thesis if \<open>nanoCoP 
    [
      Clause [
        Matrix [Clause [LitM True P],Clause [LitM False Q]],
        Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
      ],
      Clause [LitM True Q]
    ] 
  [(False, P)]\<close> using that by fast
  with ReductionMat have ?thesis if \<open>nanoCoP
    [Clause [LitM True P],Clause [LitM False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [
        Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
      ],
      Clause [LitM True Q]
    ] 
  [(False, P)]\<close> using that by fast
  with ReductionMat have ?thesis if \<open>nanoCoP
    [Clause [LitM True P],Clause [LitM False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
  [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [LitM True Q]]
  [(False, P)]\<close> using that by fast 
  with ReductionLit have ?thesis if \<open>nanoCoP
    [
      Clause [],
      Clause [LitM False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
  [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [LitM True Q]]
  [(False, P)]\<close> using that by force
  with Axiom have ?thesis if \<open>nanoCoP
    [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
  [(False, P)]\<close> using that by fast
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM False Q,LitM True R],Clause [LitM False R]]
  [(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
  [(False, P)]\<close> using that by fast
  with Axiom have ?thesis if \<open>nanoCoP
    [Clause [LitM False Q,LitM True R],Clause [LitM False R]]
  [(True, Q),(False, P)]\<close> using that by fast
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM True R],Clause [LitM False R]]
  [(True, Q),(False, P)]\<close> using that member.simps(2) by (metis (full_types))
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM False R]]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False R]]
  [(True, Q),(False, P)]\<close> using that by fastforce
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause []]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False R]]
  [(True, Q), (False, P)]\<close> using that member.simps(2) by (metis (full_types))
  with Axiom show ?thesis by fast
qed

(*could also be done with sledgehammer:*)
private lemma \<open>nanoCoP 
  [
    Clause [LitM False P],
    Clause [
      Matrix [Clause [LitM True P],Clause [LitM False Q]],
      Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
    ],
    Clause [LitM True Q]
  ] 
  []\<close> 
  by (simp add: Axiom ExtensionLit ReductionLit ReductionMat)
end

abbreviation \<open>evalLit i pol prp \<equiv> ((pol \<and> \<not>i prp) \<or> (\<not>pol \<and> i prp))\<close>

fun semanticsMat semanticsCls where
  \<open>semanticsMat i (LitM pol prp) = evalLit i pol prp\<close> |
  \<open>semanticsMat i (Matrix []) = False\<close> |
  \<open>semanticsMat i (Matrix (cls # mat)) = 
    (semanticsCls i cls \<or> semanticsMat i (Matrix mat))\<close> |
  \<open>semanticsCls i (LitC pol prp) = evalLit i pol prp\<close> | 
  \<open>semanticsCls i (Clause []) = True\<close> |
  \<open>semanticsCls i (Clause (mat # cls)) = 
    (semanticsMat i mat \<and> semanticsCls i (Clause cls))\<close>  

fun pathMat pathCls where
  \<open>pathMat path (LitM pol prp) = member (pol,prp) path\<close> | 
  \<open>pathMat path (Matrix []) = True\<close> | 
  \<open>pathMat path (Matrix (cls # mat)) = (pathCls path cls \<and> pathMat path (Matrix mat))\<close> | 
  \<open>pathCls path (LitC pol prp) = member (pol,prp) path\<close> | 
  \<open>pathCls path (Clause []) = False\<close> |
  \<open>pathCls path (Clause (mat # cls)) = (pathMat path mat \<or> pathCls path (Clause cls))\<close> 

(*Weird equality thing needed to get induction correct*)
lemma prefixPath: 
  \<open>pathMat path mat \<Longrightarrow> path' = (prefix @ path) \<Longrightarrow> pathMat path' mat\<close>
  \<open>pathCls path cls \<Longrightarrow> path' = (prefix @ path) \<Longrightarrow> pathCls path' cls\<close>
  by (induct mat and cls rule: pathMat_pathCls.induct) auto

lemma suffixPath: 
  \<open>pathMat path mat \<Longrightarrow> path' = (path @ suffix) \<Longrightarrow> pathMat path' mat\<close>
  \<open>pathCls path cls \<Longrightarrow> path' = (path @ suffix) \<Longrightarrow> pathCls path' cls\<close>
  by (induct mat and cls rule: pathMat_pathCls.induct) auto+

(* Quantifier semantics:*)
fun semanticsMatQ semanticsClsQ where
  \<open>semanticsMatQ i (LitM pol prp) = evalLit i pol prp\<close> |
  \<open>semanticsMatQ i (Matrix mat) = (\<exists> cls \<in> set mat. semanticsClsQ i cls)\<close> |
  \<open>semanticsClsQ i (LitC pol prp) = evalLit i pol prp\<close> |
  \<open>semanticsClsQ i (Clause cls) = (\<forall> cls_elem \<in> set cls. semanticsMatQ i cls_elem)\<close> 

lemma semantics_implies_semanticsQ:
  \<open>semanticsMat i mat \<Longrightarrow> semanticsMatQ i mat\<close>
  \<open>semanticsCls i cls \<Longrightarrow> semanticsClsQ i cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp_all

lemma semanticsQ_implies_semantics:
  \<open>semanticsMatQ i mat \<Longrightarrow> semanticsMat i mat\<close>
  \<open>semanticsClsQ i cls \<Longrightarrow> semanticsCls i cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp_all

fun pathMatQ pathClsQ where
  \<open>pathMatQ path (LitM pol prp) = member (pol, prp) path\<close> | 
  \<open>pathMatQ path (Matrix mat) = (\<forall> cls \<in> set mat. pathClsQ path cls)\<close> | 
  \<open>pathClsQ path (LitC pol prp) = member (pol, prp) path\<close> | 
  \<open>pathClsQ path (Clause cls) = (\<exists> cls_elem \<in> set cls. pathMatQ path cls_elem)\<close> 

lemma path_implies_pathQ:
  \<open>pathMat path mat \<Longrightarrow> pathMatQ path mat\<close>
  \<open>pathCls path cls \<Longrightarrow> pathClsQ path cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp_all

lemma pathQ_implies_path:
  \<open>pathMatQ path mat \<Longrightarrow> pathMat path mat\<close>
  \<open>pathClsQ path cls \<Longrightarrow> pathCls path cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp_all

lemma tbd:\<open>
  \<exists> prp. member (True, prp) path \<and> member (False,prp) path \<Longrightarrow>
    \<forall> i. \<exists> (pol,prp) \<in> set path. evalLit i pol prp\<close>
  by (metis (no_types, lifting) case_prodI member_iff)

(*
lemma p1:\<open>
  pathCls path cls \<Longrightarrow> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path) \<Longrightarrow>
    \<exists> i. \<not>semanticsCls i cls\<close> sorry

lemma p2:\<open>
  pathMat path mat \<Longrightarrow> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path) \<Longrightarrow>
    \<exists> i. \<not>semanticsMat i mat\<close> sorry*)


(*
lemma p3Q:\<open>
  \<not>semanticsClsQ i cls \<Longrightarrow> 
  (\<exists> path. pathClsQ path cls \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> \<open>
  \<not>semanticsMatQ i mat \<Longrightarrow> 
  (\<exists> path. pathMatQ path mat \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> 
proof (induct cls and mat)
  case (Lit pol prp)
  have \<open>pathMatQ [(pol, prp)] (Lit pol prp)\<close> 
    by simp
  then show ?case
    by fastforce
next
  case (Matrix mat)
  then have \<open>
    \<forall> cls \<in> set mat. \<exists>path. 
      pathClsQ path cls \<and> (\<nexists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path)\<close> by simp
  (*doesn't follow*)
  then show ?case sorry
next
  case (Clause cls)
  then show ?case 
    by (metis matrix_elem.inject pathClsQ.simps semanticsClsQ.elims(3))
qed

lemma p3:\<open>
  \<not>semanticsCls i cls \<Longrightarrow> 
  (\<exists> path. pathCls path cls \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> \<open>
  \<not>semanticsMat i mat \<Longrightarrow> 
  (\<exists> path. pathMat path mat \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> 
  using p3Q pathQ_implies_path semanticsQ_implies_semantics by blast+*)

(*
lemma \<open>
  (\<forall> path. pathMat path mat \<longrightarrow> (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)) \<longleftrightarrow>
    (\<forall> i. semanticsMat i mat)\<close> 
  by (meson p2 p4)

lemma \<open>
  (\<forall> path. pathCls path mat \<longrightarrow> (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)) \<longleftrightarrow>
    (\<forall> i. semanticsCls i mat)\<close> 
  by (meson p1 p3) *)

primrec sum where
  \<open>sum [] = (0 :: nat)\<close> |
  \<open>sum (x # xs) = x + sum xs\<close>

lemma sum_append: \<open>sum (xs @ ys) = sum xs + sum ys\<close>
  by (induct xs) auto

fun nodesMat nodesCls where
  \<open>nodesMat (LitM _ _) = (0 :: nat)\<close> |
  \<open>nodesMat (Matrix []) = 0\<close> |
  \<open>nodesMat (Matrix (cls # mat)) = 1 + sum (map nodesCls (cls # mat))\<close> |
  \<open>nodesCls (LitC _ _) = 0\<close> |
  \<open>nodesCls (Clause []) = 0\<close> |
  \<open>nodesCls (Clause (mat # cls)) = 1 + sum (map nodesMat (mat # cls))\<close> 

lemma add_clause_preserves_nodes: \<open>
  x < nodesMat (Matrix mat) \<Longrightarrow> x < nodesMat (Matrix (cls # mat))\<close>
proof-
  assume a:\<open>x < nodesMat (Matrix mat)\<close>
  moreover have \<open>... = 1 + sum  (map nodesCls mat)\<close>
    by (metis calculation clause_elem.inject(2) less_nat_zero_code nodesMat.elims)
  moreover have \<open>... \<le>  1 + sum  (map nodesCls (cls # mat))\<close> 
    by simp
  ultimately show ?thesis 
    using a by auto
qed

lemma nodes_in_non_empty_cls:\<open>
  \<exists> cls \<in> set mat. cls = Clause (h # t) \<Longrightarrow> 1 < nodesMat (Matrix mat)\<close> 
proof (induct mat arbitrary: h t)
  case Nil
  then show ?case 
    by simp
next
  case (Cons cls mat)
  consider \<open>cls = Clause []\<close> | \<open>\<exists> pol prp. cls = LitC pol prp\<close> | \<open>\<exists> h t. cls = Clause (h # t)\<close> 
    by (meson nodesCls.cases)
  then show ?case 
  proof cases
    case 1
    then show ?thesis
      by (metis Cons.hyps Cons.prems add_clause_preserves_nodes list.distinct(1) 
          matrix_elem.inject(2) set_ConsD)
  next
    case 2
    then show ?thesis 
      by (metis Cons.hyps Cons.prems add_clause_preserves_nodes matrix_elem.distinct(1) set_ConsD)
  next
    case 3
    then show ?thesis by auto
  qed
qed

lemma nodes_imply_non_empty_cls:\<open>
  nodesMat (Matrix mat) > 1 \<Longrightarrow> \<exists> h t. \<exists> cls \<in> set mat. cls = Clause (h # t)\<close>
proof (induct mat)
  case Nil
  then show ?case by simp
next
  case (Cons cls mat)
  consider \<open>(\<exists> pol prp. cls = LitC pol prp) \<or> cls = Clause []\<close> | \<open>\<exists> h t. cls = Clause (h # t)\<close> 
    by (metis nodesCls.cases)
  then show ?case
  proof cases
    case 1
    then have \<open>nodesCls cls = 0\<close> 
      by auto
    moreover have \<open>nodesMat (Matrix (cls # mat)) = 1 + nodesCls cls + (sum (map nodesCls mat))\<close> 
      by simp
    ultimately show ?thesis 
      by (metis Cons.hyps Cons.prems add_0_iff canonically_ordered_monoid_add_class.lessE 
          clause_elem.distinct(1) clause_elem.inject(2) list.set_intros(2) list.simps(8) 
          nanoCoP3.sum.simps(1) nodesMat.elims)
  next
    case 2
    then show ?thesis
      by auto
  qed
qed 

lemma permPath: 
  \<open>pathMat path mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow> 
    pathMat path matb\<close>
  \<open>pathCls path clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    pathCls path clsb\<close>
proof (induct mata and clsa)
  case (Matrix x)
  then show ?case 
    by (metis pathMatQ.simps(2) pathQ_implies_path(1) path_implies_pathQ(1) perm_iff)
next
  case (Clause x)
  then show ?case
    by (metis pathClsQ.simps(2) pathQ_implies_path(2) path_implies_pathQ(2) perm_iff)
qed auto

lemma permSemantics:
  \<open>semanticsMat i mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow>
    semanticsMat i matb\<close>
  \<open>semanticsCls i clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    semanticsCls i clsb\<close>
proof (induct mata and clsa)
  case (Matrix x)
  then show ?case 
    by (metis perm_iff semanticsMatQ.simps(2) semanticsQ_implies_semantics(1) 
        semantics_implies_semanticsQ(1))
next
  case (Clause x)
  then show ?case
    by (metis perm_iff semanticsClsQ.simps(2) semanticsQ_implies_semantics(2) 
        semantics_implies_semanticsQ(2))
qed auto

lemma move_to_front_perm:
  \<open>cls \<in> set mat \<Longrightarrow> perm mat (cls # remove1 cls mat)\<close>
  using in_set_remove1 by fastforce 

lemma move_to_front_sum_mat:
  \<open>cls \<in> set mat \<Longrightarrow> sum (map nodesCls mat) = sum (map nodesCls (cls # remove1 cls mat))\<close> 
  by (induct mat) auto

lemma move_to_front_sum_cls:
  \<open>mat \<in> set cls \<Longrightarrow> sum (map nodesMat cls) = sum (map nodesMat (mat # remove1 mat cls))\<close> 
  by (induct cls) auto

primrec unwrap where
  \<open>unwrap (LitM pol prp) = [LitC pol prp]\<close> |
  \<open>unwrap (Matrix mat) = mat\<close>

lemma pick_mat_semantics: \<open>
  (\<forall> i. semanticsMat i (Matrix ((Clause cls) # mat))) \<longleftrightarrow> 
  (\<forall> mat' \<in> set cls. \<forall> i. 
    semanticsMat i (Matrix ((unwrap mat') @ mat)))\<close> sorry

lemma pick_mat_paths: \<open>
  (
    \<forall> path. pathMat path (Matrix ((Clause cls) # mat)) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
  ) \<longleftrightarrow> 
  (
    \<forall> mat' \<in> set cls. 
       \<forall> path. pathMat path (Matrix ((unwrap mat') @ mat)) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
  )\<close> sorry

lemma pick_mat_nodes: \<open>
  mat' \<in> set cls \<Longrightarrow>
    nodesMat (Matrix ((Clause cls) # mat)) > nodesMat (Matrix ((unwrap mat') @ mat))\<close> 
  (is \<open>?mat \<Longrightarrow> ?nodes\<close>) 
proof-
  assume mat'_def: ?mat
  have cls_mat_nodes:\<open>
    nodesMat (Matrix ((Clause cls) # mat)) = 
    1 + nodesCls (Clause cls) + sum (map nodesCls mat)\<close>
    by simp
  have cls_nodes:\<open>
    nodesCls (Clause cls) = 1 + nodesMat mat' + sum (map nodesMat (remove1 mat' cls))\<close> 
    using mat'_def move_to_front_sum_cls 
    by (smt (verit, ccfv_threshold) ab_semigroup_add_class.add_ac(1) list.set_cases list.simps(9) 
        nanoCoP3.sum.simps(2) nodesCls.simps(3))
  consider \<open>\<exists> pol prp. mat' = LitM pol prp\<close> | \<open>\<exists> matI'. mat' = Matrix matI'\<close> 
    by (meson clause_elem.exhaust)
  then show ?nodes 
  proof cases
    case 1
    then show ?thesis 
      using append_eq_append_conv2 cls_nodes by auto
  next
    case 2
    consider (21)\<open>unwrap mat' @ mat = []\<close> | (22)\<open>unwrap mat' @ mat \<noteq> []\<close> 
      by fast
    then show ?thesis 
    proof cases
      case 21
      then show ?thesis 
        by simp
    next
      case 22
      then have \<open>
        nodesMat (Matrix (unwrap mat' @ mat)) = 
        1 + sum (map nodesCls (unwrap mat')) + sum (map nodesCls mat)\<close> 
        using sum_append 
        by (metis clause_elem.distinct(1) clause_elem.inject(2) group_cancel.add1 map_append 
            nodesMat.elims)
      then show ?thesis 
        by (metis "2" add.commute add_strict_right_mono clause_elem.distinct(1) cls_mat_nodes 
            cls_nodes less_add_same_cancel1 list.simps(8) nanoCoP3.sum.simps(1) nodesMat.elims 
            trans_less_add1 unwrap.simps(2) zero_less_one)
    qed
  qed
qed

primrec lit_to_path_elem where
  \<open>lit_to_path_elem (LitC pol prp) = (pol,prp)\<close> |
  \<open>lit_to_path_elem (Clause mat) = undefined\<close>

lemma flat_matrix_syntactic_to_semantic: \<open>
  \<forall> cls \<in> set mat. \<exists> pol prp. cls = LitC pol prp \<Longrightarrow>
    (
      \<forall> path. pathMat path (Matrix mat) \<longrightarrow> 
      (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
    ) \<longleftrightarrow>
    (\<forall> i. semanticsMat i (Matrix mat))\<close> (is \<open>?flat \<Longrightarrow> ?paths \<longleftrightarrow> ?valid\<close>)
proof-
  assume asm1:?flat
  then have all_paths:\<open>
    \<forall> path. \<forall> cls \<in> set mat.
      pathMat path (Matrix mat) \<longrightarrow>
      (\<exists> pol prp. cls = LitC pol prp \<and> (pol,prp) \<in> set path)\<close>
    by (metis member_iff pathClsQ.simps(1) pathMatQ.simps(2) path_implies_pathQ(1))
  show \<open>?paths \<longleftrightarrow> ?valid\<close>
  proof (rule iffI, rule_tac [!] allI)
    fix i
    assume asm2:?paths
    have \<open>\<exists> prp. LitC True prp \<in> set mat \<and> LitC False prp \<in> set mat\<close>
    proof (rule ccontr)
      assume asm3:\<open>\<nexists> prp. LitC True prp \<in> set mat \<and> LitC False prp \<in> set mat\<close>
      obtain path where path_def:\<open>path = map lit_to_path_elem mat\<close>
        by simp
      have lit_in_path_in_mat:
        \<open>\<forall> lit \<in> set path. \<exists> pol prp. lit = (pol,prp) \<and> LitC pol prp \<in> set mat\<close> 
      proof
        fix lit
        assume asm4:\<open>lit \<in> set path\<close>
        obtain pol prp where lit_def:\<open>lit = (pol,prp)\<close> 
          by fastforce
        then obtain cls where cls_def: \<open>cls \<in> set mat \<and> lit = lit_to_path_elem cls\<close> 
          using asm4 path_def by auto
        then have \<open>cls = LitC pol prp\<close>
          using lit_def asm1 by (metis Pair_inject lit_to_path_elem.simps(1))
        then show \<open>\<exists> pol prp. lit = (pol,prp) \<and> LitC pol prp \<in> set mat\<close>
          using cls_def by auto
      qed
      then have \<open>\<nexists> prp. (True, prp) \<in> set path \<and> (False, prp) \<in> set path\<close> 
        using asm1 asm3 by blast 
      moreover have \<open>pathMat path (Matrix mat)\<close>
        using lit_in_path_in_mat 
        by (metis asm1 in_set_conv_nth length_map lit_to_path_elem.simps(1) matrix_elem.distinct(1) 
            member_iff nth_map pathClsQ.elims(3) pathMatQ.simps(2) pathQ_implies_path(1) path_def)
      ultimately show False 
        using asm2 by blast
    qed
    then show \<open>semanticsMat i (Matrix mat)\<close>
      by (metis move_to_front_perm permSemantics(1) semanticsCls.simps(1) semanticsMat.simps(3))
  next
    fix path
    assume asm2:?valid
    show \<open>pathMat path (Matrix mat) \<longrightarrow> (\<exists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path)\<close>
    proof (rule impI, rule ccontr)
      assume asm3:\<open>pathMat path (Matrix mat)\<close>
      assume asm4:\<open>\<nexists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path\<close>
      then have nexi_prp:\<open>\<nexists>prp. LitC True prp \<in> set mat \<and> LitC False prp \<in> set mat\<close> 
        using all_paths asm3 by blast
      obtain i where i_def:\<open>i = (\<lambda> prp. LitC True prp \<in> set mat)\<close>
        by simp
      have \<open>\<not>semanticsMatQ i (Matrix mat)\<close>
        using asm1 i_def nexi_prp by fastforce
      then have \<open>\<not>semanticsMat i (Matrix mat)\<close>
        using semantics_implies_semanticsQ(1) by blast
      then show False
        using asm2 by simp
    qed
  qed
qed
 
lemma syntactic_to_semantic_validity:\<open>
  (\<forall> path. pathMat path mat \<longrightarrow> (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)) \<longleftrightarrow>
  (\<forall> i. semanticsMat i mat)\<close>
proof (induct \<open>nodesMat mat\<close> arbitrary: mat rule: less_induct)
  case less
  consider (0)\<open>nodesMat mat = 0\<close> | (1)\<open>nodesMat mat = 1\<close> | (n)\<open>1 < nodesMat mat\<close>
    by linarith
  then show ?case
  proof cases
    case 0
    then consider \<open>\<exists> pol prp. mat = LitM pol prp\<close> | \<open>mat = Matrix []\<close> 
      by (metis add_eq_0_iff_both_eq_0 nodesMat.elims zero_neq_one)
    then show ?thesis 
    proof cases
      case 1
      then obtain pol prp where mat_def: \<open>mat = LitM pol prp\<close> 
        by auto
      moreover obtain i where \<open>i prp = pol\<close>
        by simp
      ultimately have \<open>\<not>semanticsMat i mat\<close> 
        by simp
      moreover have \<open>pathMat [(pol,prp)] mat\<close> 
        by (simp add: mat_def)
      ultimately show ?thesis 
        by auto
    next
      case 2
      then show ?thesis
        by (meson in_set_member member_rec(2) pathMat.simps(2) semanticsMat.simps(2))
    qed
  next
    case 1
    then obtain matI where mat_def:\<open>mat = Matrix matI\<close> 
      by (metis clause_elem.exhaust nodesMat.simps(1) zero_neq_one)
    have \<open>\<forall> cls \<in> set matI. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp)\<close>
    proof (rule ccontr)
      assume \<open>\<not> (\<forall>cls\<in>set matI. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp))\<close>
      then obtain cls h t where \<open>cls \<in> set matI \<and> cls = Clause (h # t)\<close>
        by (meson nodesCls.cases)
      then have \<open>nodesMat mat > 1\<close> 
        using mat_def nodes_in_non_empty_cls by auto
      then show False 
        by (simp add: "1")
    qed
    then consider 
      (ex)\<open>\<exists> cls \<in> set matI. cls = Clause []\<close> | 
      (al)\<open>\<forall> cls \<in> set matI. (\<exists> pol prp. cls = LitC pol prp)\<close>
      by blast
    then show ?thesis 
    proof cases
      case ex
      then have \<open>perm matI (Clause [] # remove1 (Clause []) matI)\<close> 
        by (meson move_to_front_perm)
      then show ?thesis 
        by (metis mat_def pathCls.simps(2) pathMat.simps(3) permPath(1) permSemantics(1) 
            semanticsCls.simps(2) semanticsMat.simps(3))
    next
      case al
      then show ?thesis
        by (simp add: flat_matrix_syntactic_to_semantic mat_def)
    qed
  next
    case n
    then obtain matI where mat_def:\<open>mat = Matrix matI\<close> 
      by (metis clause_elem.exhaust less_nat_zero_code nodesMat.simps(1))
    then obtain clsh clst where cls_def:\<open>Clause (clsh # clst) \<in> set matI\<close> 
      using nodes_imply_non_empty_cls n by blast

    let ?cls = \<open>Clause (clsh # clst)\<close>
    let ?paths_cls_in_front = \<open>
      (
        \<forall>path. pathMat path (Matrix (?cls # remove1 ?cls matI)) \<longrightarrow> 
        (\<exists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path)
      )\<close>
    let ?semantics_cls_in_front = \<open>(\<forall>i. semanticsMat i (Matrix (?cls # remove1 ?cls matI)))\<close>
    
    have unwrapped_nodes: \<open>\<forall> mat' \<in> set (clsh # clst).
        nodesMat (Matrix (unwrap mat' @ remove1 ?cls matI)) < nodesMat mat\<close>  
      by (metis cls_def mat_def move_to_front_sum_mat n nodesMat.elims nodesMat.simps(3) 
          not_one_less_zero pick_mat_nodes unwrap.simps(2))
    have \<open>
      ?paths_cls_in_front \<longleftrightarrow>
      (
        \<forall> mat' \<in> set (clsh # clst). 
           \<forall> path. pathMat path (Matrix (unwrap mat' @ remove1 ?cls matI)) \<longrightarrow> 
        (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
      )\<close> 
      using pick_mat_paths by fast
    moreover have \<open>
      ... \<longleftrightarrow>
      (
        \<forall> mat' \<in> set (clsh # clst).
          \<forall> i. semanticsMat i (Matrix (unwrap mat' @ remove1 ?cls matI))
      )\<close>
        using less unwrapped_nodes by fastforce
    moreover have \<open>
      ... \<longleftrightarrow> ?semantics_cls_in_front\<close>
      using pick_mat_semantics by blast
    ultimately have \<open>?paths_cls_in_front \<longleftrightarrow> ?semantics_cls_in_front\<close>
      by blast
    then show ?thesis 
      using mat_def move_to_front_perm by (metis cls_def permPath(1) permSemantics(1))
  qed
qed

theorem path_soundness: 
  \<open>nanoCoP mat path \<Longrightarrow> \<forall> path'. ext path' path \<longrightarrow> pathMat path' (Matrix mat) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path' \<and> (True,prp) \<in> set path')\<close>
proof (induct rule: nanoCoP.induct)
  case (Axiom Mat Path)
  then show ?case
    by simp
next
  case (PermMat Mat1 Path Mat2)
  then show ?case 
    using permPath(1) by blast
next
  case (PermCls Cls1 Cls2 Mat Path)
  then show ?case
    by (meson pathMat.simps(3) permPath(2))
next
  case (ReductionLit pol prp Path Cls Mat)
  then show ?case 
    by (smt (verit) ext_iff member_iff pathCls.simps(3) pathMat.simps(1) pathMat.simps(3))
next
  case (ReductionMat mat Path Cls Mat)
  then show ?case 
    by auto
next
  case (ExtensionLit Mat pol prp Path Cls)
  then show ?case 
    by (metis ext.simps(2) pathCls.simps(3) pathMat.simps(1) pathMat.simps(3))
next
  case (ExtensionMat mat Mat Path Cls)
  then show ?case
    by auto
next
  case (ReductionLitC pol prp Path Mat)
  then show ?case 
    by (smt (verit, del_insts) ext_iff member_iff pathCls.simps(1) pathMat.simps(3))
next
  case (ExtensionLitC Mat pol prp Path)
  then show ?case
    by simp
qed

theorem soundness: \<open>nanoCoP mat [] \<Longrightarrow> (\<forall> i. semanticsMat i (Matrix mat))\<close> 
  by (meson ext.simps(1) syntactic_to_semantic_validity path_soundness)

theorem main: \<open>nanoCoP mat [] \<longleftrightarrow> (\<forall> i. semanticsMat i (Matrix mat))\<close> sorry

end