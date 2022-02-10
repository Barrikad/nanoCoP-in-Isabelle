theory nanoCoP2 imports Main
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

lemma ext_iff: \<open>ext ys xs \<longleftrightarrow> (\<forall> x \<in> set xs. x \<in> set ys)\<close>
  by (induct xs) auto

abbreviation \<open>perm xs ys \<equiv> ext xs ys \<and> ext ys xs\<close>

lemma perm_iff [iff]: \<open>perm xs ys \<longleftrightarrow> set xs = set ys\<close>
  using ext_iff by (induct xs) auto

(*LitC rules and PathAxiom are necessary because of the way we define the path semantics*)
inductive nanoCoP where
  Axiom: 
    \<open>nanoCoP (Clause [] # Mat) Path\<close> |
  PathAxiom:
    \<open>nanoCoP Mat Path\<close> if
    \<open>member (True,prp) Path\<close> and
    \<open>member (False,prp) Path\<close>|
  ExtMat: 
    \<open>nanoCoP Mat2 Path\<close> if 
    \<open>ext Mat2 Mat1\<close> and
    \<open>nanoCoP Mat1 Path\<close> |
  ExtCls: 
    \<open>nanoCoP (Clause Cls2 # Mat) Path\<close> if 
    \<open>ext Cls1 Cls2\<close> and 
    \<open>nanoCoP (Clause Cls1 # Mat) Path\<close> |
  ReductionLit: 
    \<open>nanoCoP (Clause (LitM pol prp # Cls) # Mat) Path\<close> if
    \<open>member (\<not>pol, prp) Path\<close> and 
    \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ReductionLitC: 
    \<open>nanoCoP (LitC pol prp # Mat) Path\<close> if 
    \<open>member (\<not>pol, prp) Path\<close> |
  ExtensionLit: 
    \<open>nanoCoP (Clause (LitM pol prp # Cls) # Mat) Path\<close> if
    \<open>nanoCoP Mat ((pol, prp) # Path)\<close> and
    \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ExtensionLitC: 
    \<open>nanoCoP (LitC pol prp # Mat) Path\<close> if
    \<open>nanoCoP Mat ((pol, prp) # Path)\<close> |
  ExtensionMat: 
    \<open>nanoCoP (Clause (Matrix mat # Cls) # Mat) Path\<close> if
    \<open>nanoCoP (mat @ Mat) Path\<close> and
    \<open>nanoCoP (Clause Cls # Mat) Path\<close>

(*Example proofs*)
context begin
private datatype props = P | Q | R

private lemma \<open>nanoCoP
  [
    Clause [Matrix [LitC True P]],
    Clause [Matrix [LitC False P]]
  ]
  []\<close>
proof-
  have \<open>nanoCoP
  [
    Clause [Matrix [LitC False P]],
    LitC True P
  ]
  []\<close> by (simp add: ExtensionLitC ReductionLitC Axiom ExtensionMat)
  then have \<open>nanoCoP
  [
    LitC True P,
    Clause [Matrix [LitC False P]]
  ]
  []\<close> using ExtMat by force
  then show ?thesis 
    by (simp add: Axiom ExtensionMat)
qed

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
  with ExtensionMat have ?thesis if \<open>nanoCoP
    [Clause [LitM True P],Clause [LitM False Q],Clause [LitM True Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [
        Matrix [Clause [LitM True Q],Clause [LitM False Q,LitM True R],Clause [LitM False R]]
      ],
      Clause [LitM True Q]
    ] 
  [(False, P)]\<close> using that by (metis append.left_neutral append_Cons)
  with ExtensionMat have ?thesis if \<open>nanoCoP
    [Clause [LitM True P],Clause [LitM False Q],Clause [LitM True Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [LitM True Q],
      Clause [LitM False Q,LitM True R],
      Clause [LitM False R],
      Clause [LitM True Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [LitM True Q]]
  [(False, P)]\<close> using that by (metis append.left_neutral append_Cons)
  with ReductionLit have ?thesis if \<open>nanoCoP
    [
      Clause [],Clause [LitM False Q],Clause [LitM True Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [LitM True Q],
      Clause [LitM False Q,LitM True R],
      Clause [LitM False R],
      Clause [LitM True Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [LitM True Q]]
  [(False, P)]\<close> using that by (smt (verit, best) member.simps(2))
  with Axiom have ?thesis if \<open>nanoCoP
    [
      Clause [LitM True Q],
      Clause [LitM False Q,LitM True R],
      Clause [LitM False R],
      Clause [LitM True Q]]
    [(False, P)]\<close> using that by fast
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM False Q,LitM True R],Clause [LitM False R],Clause [LitM True Q]]
  [(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False Q,LitM True R],Clause [LitM False R],Clause [LitM True Q]]
  [(False, P)]\<close> using that by fast
  with Axiom have ?thesis if \<open>nanoCoP
    [Clause [LitM False Q,LitM True R],Clause [LitM False R],Clause [LitM True Q]]
  [(True, Q),(False, P)]\<close> using that by fast
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM True R],Clause [LitM False R],Clause [LitM True Q]]
  [(True, Q),(False, P)]\<close> using that member.simps(2) by (smt (verit, best))
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [LitM False R],Clause [LitM True Q]]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False R],Clause [LitM True Q]]
  [(True, Q),(False, P)]\<close> using that by fastforce
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause [],Clause [LitM True Q]]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [LitM False R],Clause [LitM True Q]]
  [(True, Q), (False, P)]\<close> using that member.simps(2) by (smt (verit, best))
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
  by (simp add: Axiom ExtensionLit ReductionLit ExtensionMat)
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
          sum.simps(1) nodesMat.elims)
  next
    case 2
    then show ?thesis
      by auto
  qed
qed 

lemma extPath:
  \<open>pathMat path mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> ext mat1 mat2 \<Longrightarrow>
    pathMat path matb\<close>
  \<open>pathCls path clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> ext cls2 cls1 \<Longrightarrow>
    pathCls path clsb\<close>
   apply (meson ext_iff pathMatQ.simps(2) pathQ_implies_path(1) path_implies_pathQ(1))
  by (meson ext_iff pathClsQ.simps(2) pathQ_implies_path(2) path_implies_pathQ(2))

lemma permPath: 
  \<open>pathMat path mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow> 
    pathMat path matb\<close>
  \<open>pathCls path clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    pathCls path clsb\<close> 
  by (meson extPath)+

lemma extSemantics:
  \<open>semanticsMat i mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> ext mat2 mat1 \<Longrightarrow>
    semanticsMat i matb\<close>
  \<open>semanticsCls i clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> ext cls1 cls2 \<Longrightarrow>
    semanticsCls i clsb\<close> 
   apply (metis ext_iff semanticsMatQ.simps(2) semanticsQ_implies_semantics(1) 
          semantics_implies_semanticsQ(1))
  by (metis ext_iff semanticsClsQ.simps(2) semanticsQ_implies_semantics(2) 
      semantics_implies_semanticsQ(2))

lemma permSemantics:
  \<open>semanticsMat i mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow>
    semanticsMat i matb\<close>
  \<open>semanticsCls i clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    semanticsCls i clsb\<close>
  by (meson extSemantics)+

lemma move_to_front_perm:
  \<open>cls \<in> set mat \<Longrightarrow> perm mat (cls # remove1 cls mat)\<close>
  using in_set_remove1 by fastforce

lemma move_to_front_sum_mat:
  \<open>cls \<in> set mat \<Longrightarrow> sum (map nodesCls mat) = sum (map nodesCls (cls # remove1 cls mat))\<close> 
  by (induct mat) auto

lemma move_to_front_sum_cls:
  \<open>mat \<in> set cls \<Longrightarrow> sum (map nodesMat cls) = sum (map nodesMat (mat # remove1 mat cls))\<close> 
  by (induct cls) auto

lemma split_matrix_preserves_semantics: \<open>
  semanticsMat i (Matrix (mat1 @ mat2)) \<longleftrightarrow> 
  semanticsMat i (Matrix mat1) \<or> semanticsMat i (Matrix mat2)\<close> 
  by (induct mat1) simp_all

primrec unwrap where
  \<open>unwrap (LitM pol prp) = [LitC pol prp]\<close> |
  \<open>unwrap (Matrix mat) = mat\<close>

lemma pick_mat_semantics: \<open>
  (\<forall> i. semanticsMat i (Matrix ((Clause cls) # mat))) \<longleftrightarrow> 
  (\<forall> mat' \<in> set cls. \<forall> i. 
    semanticsMat i (Matrix ((unwrap mat') @ mat)))\<close> (is \<open>?cls \<longleftrightarrow> ?uwmat\<close>)
proof (rule iffI, rule_tac [1] ballI, rule_tac [!] allI)
  fix i mat'
  assume asm1:\<open>mat' \<in> set cls\<close>
  assume asm2:?cls
  then have \<open>semanticsMat i (Matrix ((Clause cls) # mat))\<close> 
    by simp
  then consider \<open>semanticsCls i (Clause cls)\<close> | \<open>semanticsMat i (Matrix mat)\<close>
    by auto
  then show \<open>semanticsMat i (Matrix (unwrap mat' @ mat))\<close> 
  proof cases
    case 1
    then have \<open>semanticsMat i mat'\<close>
      by (metis asm1 ext.simps(2) member_iff permSemantics(2) perm_iff semanticsCls.simps(3))
    then show ?thesis
      by (smt (verit, del_insts) list.inject not_Cons_self2 semanticsCls.simps(1) 
          semanticsMat.elims(2) semanticsMat.elims(3) split_matrix_preserves_semantics 
          unwrap.simps(1) unwrap.simps(2))
  next
    case 2
    then show ?thesis 
      by (simp add: split_matrix_preserves_semantics) 
  qed
next
  fix i
  assume asm1:?uwmat
  have \<open>\<forall> mat' \<in> set cls. semanticsMat i mat' \<or> semanticsMat i (Matrix mat)\<close> 
  proof (rule ccontr)
    assume asm2: \<open>\<not> (\<forall>mat'\<in>set cls. semanticsMat i mat' \<or> semanticsMat i (Matrix mat))\<close>
    then obtain mat' where mat'_def:\<open>mat' \<in> set cls \<and> \<not>semanticsMat i mat'\<close>
      by auto
    then have \<open>\<not>semanticsMat i (Matrix (unwrap mat'))\<close>
    proof (cases mat')
    qed auto
    then show False 
      using asm1 asm2 mat'_def split_matrix_preserves_semantics by blast
  qed
  then consider \<open>\<forall> mat' \<in> set cls. semanticsMat i mat'\<close> | \<open>semanticsMat i (Matrix mat)\<close> 
    by fast
  then show \<open>semanticsMat i (Matrix (Clause cls # mat))\<close> 
  proof cases
    case 1
    then have \<open>semanticsClsQ i (Clause cls)\<close> 
      by (simp add: semantics_implies_semanticsQ(1))
    then show ?thesis
      by (simp add: semanticsQ_implies_semantics(2))
  next
    case 2
    then show ?thesis
      by simp
  qed
qed

lemma split_matrix_preserves_path:\<open>
  pathMat path (Matrix (mat1 @ mat2)) \<longleftrightarrow> pathMat path (Matrix mat1) \<and> pathMat path (Matrix mat2)\<close> 
  by (induct mat1) simp_all

lemma pick_mat_paths: \<open>
  (
    \<forall> path. pathMat path (Matrix ((Clause cls) # mat)) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
  ) \<longleftrightarrow> 
  (
    \<forall> mat' \<in> set cls. 
       \<forall> path. pathMat path (Matrix ((unwrap mat') @ mat)) \<longrightarrow>
      (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)
  )\<close> (is \<open>?cls \<longleftrightarrow> ?uwmat\<close>)
proof (rule iffI, rule_tac [1] ballI, rule_tac [!] allI, rule_tac[!] impI)
  fix path mat'
  assume asm1: ?cls
  assume asm2:\<open>mat' \<in> set cls\<close>
  assume asm3:\<open>pathMat path (Matrix (unwrap mat' @ mat))\<close>
  have \<open>pathMat path (Matrix ((Clause cls) # mat))\<close> 
  proof (cases mat')
    case (LitM pol prp)
    then show ?thesis
      using asm2 asm3 clause_elem.inject(1) pathCls.simps(1) pathQ_implies_path(2) by force
  next
    case (Matrix matI')
    then show ?thesis
      by (metis asm2 asm3 pathClsQ.simps(2) pathMat.simps(3) pathQ_implies_path(2) 
          path_implies_pathQ(1) split_matrix_preserves_path unwrap.simps(2))
  qed
  then show \<open>\<exists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path\<close>
    by (simp add: asm1)
next
  fix path
  assume asm1: \<open>
    \<forall>mat'\<in>set cls. \<forall>path.
       pathMat path (Matrix (unwrap mat' @ mat)) \<longrightarrow>
       (\<exists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path)\<close>
  assume asm2: \<open>pathMat path (Matrix (Clause cls # mat))\<close>
  then obtain mat' where mat'_def: \<open>mat' \<in> set cls \<and> pathMat path mat'\<close> 
    by (meson list.set_intros(1) pathClsQ.simps(2) pathMatQ.simps(2) pathQ_implies_path(1) 
        path_implies_pathQ(1))
  have \<open>pathMat path (Matrix (unwrap mat' @ mat))\<close> 
  proof (cases mat')
    case (LitM pol prp)
    then show ?thesis
      using asm2 mat'_def by auto
  next
    case (Matrix matI')
    then show ?thesis
      using asm2 mat'_def split_matrix_preserves_path by auto
  qed
  then show \<open>
    (\<exists>prp. (False, prp) \<in> set path \<and> (True, prp) \<in> set path)\<close>
    using mat'_def asm1 by blast
qed

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
        sum.simps(2) nodesCls.simps(3))
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
            cls_nodes less_add_same_cancel1 list.simps(8) sum.simps(1) nodesMat.elims 
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

lemma one_node_implies_flat: \<open>
  nodesMat mat = 1 \<Longrightarrow> 
  \<exists> matI. mat = Matrix matI \<and> 
  (\<forall> cls \<in> set matI. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp))\<close> (is \<open>?nds \<Longrightarrow> ?matI\<close>) 
proof-
  assume asm1: \<open>nodesMat mat = 1\<close>
  then obtain matI where mat_def: \<open>mat = Matrix matI\<close> 
    by (metis clause_elem.exhaust nodesMat.simps(1) zero_neq_one)
  moreover have \<open>\<forall> cls \<in> set matI. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp)\<close>  
    by (metis asm1 less_numeral_extra(4) mat_def nodesCls.cases nodes_in_non_empty_cls)
  ultimately show ?matI 
    by simp
qed

(*custom mat induction, dunno how to use
lemma mat_induction: \<open>
  (mat = Matrix [] \<Longrightarrow> thesis mat) &&& 
  (\<exists> pol prp. mat = LitM pol prp \<Longrightarrow> thesis mat) &&&
  (\<exists> matI. mat = Matrix matI \<and> (\<forall> cls \<in> set matI. \<exists> pol prp. cls = LitC pol prp) \<Longrightarrow> thesis mat) &&&
  (nodesMat mat > 1 \<and> (\<forall> mat'. nodesMat mat' < nodesMat mat \<longrightarrow> thesis mat') \<Longrightarrow> thesis mat) \<Longrightarrow>
  \<forall> mat. thesis mat\<close> sorry*)

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
    then obtain matI where mat_def:\<open>
      mat = Matrix matI \<and> (\<forall> cls \<in> set matI. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp))\<close> 
      using one_node_implies_flat by blast
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

theorem path_soundness: \<open>
  nanoCoP mat path \<Longrightarrow> 
    \<forall> path'. ext path' path \<longrightarrow> pathMat path' (Matrix mat) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path' \<and> (True,prp) \<in> set path')\<close>
proof (induct rule: nanoCoP.induct)
  case (Axiom Mat Path)
  then show ?case
    by simp
next
  case (PathAxiom prp Path Mat)
  then show ?case
    by (metis (full_types) ext_iff member_iff)
next
  case (ExtMat Mat1 Path Mat2)
  then show ?case 
    using extPath(1) by blast
next
  case (ExtCls Cls1 Cls2 Mat Path)
  then show ?case  
    by (meson extPath(2) pathMat.simps(3))
next
  case (ReductionLit pol prp Path Cls Mat)
  then show ?case 
    by (smt (verit) ext_iff member_iff pathCls.simps(3) pathMat.simps(1) pathMat.simps(3))
next
  case (ExtensionLit Mat pol prp Path Cls)
  then show ?case 
    by (metis ext.simps(2) pathCls.simps(3) pathMat.simps(1) pathMat.simps(3))
next
  case (ExtensionMat mat Mat Path Cls)
  then show ?case 
    by (metis pathCls.simps(3) pathMat.simps(3) split_matrix_preserves_path)
next
  case (ReductionLitC pol prp Path Mat)
  then show ?case 
    by (smt (verit, del_insts) ext_iff member_iff pathCls.simps(1) pathMat.simps(3))
next
  case (ExtensionLitC Mat pol prp Path)
  then show ?case
    by simp
qed

theorem soundness: \<open>nanoCoP mat [] \<Longrightarrow> \<forall> i. semanticsMat i (Matrix mat)\<close> 
  by (meson ext.simps(1) syntactic_to_semantic_validity path_soundness)

lemma cls_path_gives_mat_path: \<open>
  \<forall> cls \<in> set mat. \<exists> path'. pathCls path' cls \<Longrightarrow> \<exists> path. pathMat path (Matrix mat)\<close> 
proof (induct mat)
  case Nil
  then show ?case 
    by simp
next
  case (Cons cls mat)
  then obtain path where \<open>pathMat path (Matrix mat)\<close>
    by auto
  moreover obtain path' where \<open>pathCls path' cls\<close>
    using Cons.prems by auto
  ultimately show ?case
    by (meson pathMat.simps(3) prefixPath(2) suffixPath(1))
qed

lemma extract_head_nodes: \<open>
  mat \<noteq> [] \<Longrightarrow> nodesMat (Matrix (cls # mat)) = nodesCls cls + nodesMat (Matrix mat)\<close> 
proof-
  assume asm: \<open>mat \<noteq> []\<close>
  then obtain hmat tmat where \<open>mat = hmat # tmat\<close> 
    using list.exhaust by blast
  then show \<open>nodesMat (Matrix (cls # mat)) = nodesCls cls + nodesMat (Matrix mat)\<close> 
    by simp
qed

lemma shuffle_nodes: \<open>
  cls \<in> set mat \<Longrightarrow> nodesMat (Matrix mat) = nodesMat (Matrix (cls # remove1 cls mat))\<close> 
proof (induct mat)
  case Nil
  then show ?case 
    by simp
next
  case (Cons cls' mat)
  then consider \<open>cls' = cls\<close> | \<open>cls' \<noteq> cls\<close>
    by force
  then show ?case 
  proof cases
    case 1
    then show ?thesis 
      by simp
  next
    case 2
    then have \<open>nodesMat (Matrix mat) = nodesMat (Matrix (cls # remove1 cls mat))\<close>
      using Cons.hyps Cons.prems by fastforce
    moreover have \<open>remove1 cls (cls' # mat) = cls' # remove1 cls mat\<close> 
      using "2" by auto
    moreover have \<open>nodesMat (Matrix (cls' # mat)) = nodesCls cls' + nodesMat (Matrix mat)\<close> 
      by (metis "2" Cons.prems extract_head_nodes length_greater_0_conv length_pos_if_in_set 
          set_ConsD)
    ultimately show ?thesis 
      by auto
  qed
qed

fun sizeM sizeC where 
  \<open>sizeM (LitM pol prp) = 1\<close> |
  \<open>sizeM (Matrix mat) = 1 + sum (map sizeC mat)\<close> |
  \<open>sizeC (LitC pol prp) = 1\<close> |
  \<open>sizeC (Clause cls) = 1 + sum (map sizeM cls)\<close>

lemma shuffle_size_mat: \<open>
  cls \<in> set mat \<Longrightarrow> sizeM (Matrix mat) = sizeM (Matrix (cls # remove1 cls mat))\<close> 
  by (induct mat) auto

lemma shuffle_size_cls: \<open>
  mat \<in> set cls \<Longrightarrow> sizeC (Clause cls) = sizeC (Clause (mat # remove1 mat cls))\<close> 
  by (induct cls) auto

lemma unwrap_size_mat: \<open>
  sizeM mat \<ge> sum (map sizeC (unwrap mat))\<close>  
proof-
  consider \<open>\<exists> pol prp. mat = LitM pol prp\<close> | \<open>\<exists> matI. mat = Matrix matI\<close> 
    by (meson sizeM.cases)
  then show ?thesis
  proof cases
  qed auto
qed

lemma pick_mat_size: \<open>
  mat' \<in> set cls \<Longrightarrow>
    sizeM (Matrix ((Clause cls) # mat)) > sizeM (Matrix ((unwrap mat') @ mat))\<close> (is \<open>?asm \<Longrightarrow> ?cnc\<close>)
proof-
  assume asm:?asm
  then have 1:\<open>sizeC (Clause cls) = sizeC (Clause (mat' # remove1 mat' cls))\<close> 
    by (metis shuffle_size_cls)
  have 2:\<open>sum (map sizeM (mat' # remove1 mat' cls)) \<ge> sum (map sizeC (unwrap mat'))\<close> 
  proof-
    have \<open>sum (map sizeM (mat' # remove1 mat' cls)) \<ge> sizeM mat'\<close> 
      by simp
    moreover have \<open>sizeM mat' \<ge> sum (map sizeC (unwrap mat'))\<close>  
      by (simp add: unwrap_size_mat)
    ultimately show ?thesis 
      using le_trans by blast
  qed
  have \<open>
    sizeM (Matrix ((Clause cls) # mat)) = 
    sizeM (Matrix ((Clause (mat' # remove1 mat' cls)) # mat))\<close> 
    using "1" by auto
  moreover have \<open>... = 1 + sizeC (Clause (mat' # remove1 mat' cls)) + sum (map sizeC mat)\<close>
    by simp
  moreover have \<open>... > 1 + sum (map sizeC (unwrap mat')) + sum (map sizeC mat)\<close> 
    using "2" by auto
  moreover have \<open>
    1 + sum (map sizeC (unwrap mat')) + sum (map sizeC mat) = 
  sizeM (Matrix ((unwrap mat') @ mat))\<close> 
    using sum_append by simp
  ultimately show ?cnc 
    by presburger
qed

fun containsMat containsCls where
  \<open>containsMat pol prp (LitM pol' prp') = (pol = pol' \<and> prp = prp')\<close> |
  \<open>containsMat pol prp (Matrix mat) = (\<exists> cls \<in> set mat. containsCls pol prp cls)\<close> |
  \<open>containsCls pol prp (LitC pol' prp') = (pol = pol' \<and> prp = prp')\<close> | 
  \<open>containsCls pol prp (Clause cls) = (\<exists> mat \<in> set cls. containsMat pol prp mat)\<close>

abbreviation \<open>minPathM path mat \<equiv> 
  pathMat path mat \<and> (\<forall> (pol,prp) \<in> set path. containsMat pol prp mat)\<close>

abbreviation \<open>minPathC path cls \<equiv> 
  pathCls path cls \<and> (\<forall> (pol,prp) \<in> set path. containsCls pol prp cls)\<close>

lemma size_not_0_mat: \<open>sizeM mat \<ge> 1\<close>
proof (rule ccontr)
  assume \<open>\<not>sizeM mat \<ge> 1\<close>
  moreover have \<open>(\<exists> pol prp. mat = LitM pol prp) \<or> (\<exists> matI. mat = Matrix matI)\<close>
    by (meson sizeM.cases)
  ultimately show False by force
qed

lemma size_not_0_cls: \<open>sizeC cls \<ge> 1\<close>
proof (rule ccontr)
  assume \<open>\<not>sizeC cls \<ge> 1\<close>
  moreover have \<open>(\<exists> pol prp. cls = LitC pol prp) \<or> (\<exists> clsI. cls = Clause clsI)\<close>
    by (meson sizeC.cases)
  ultimately show False by force
qed

lemma size_1_options_mat: \<open>sizeM mat = 1 \<Longrightarrow> mat = Matrix [] \<or> (\<exists> pol prp. mat = LitM pol prp)\<close>
proof (rule ccontr)
  assume asm:\<open>sizeM mat = 1\<close>
  assume \<open>\<not> (mat = Matrix [] \<or> (\<exists>pol prp. mat = LitM pol prp))\<close>
  then obtain cls matI where \<open>mat = Matrix (cls # matI)\<close>
    by (meson nodesMat.cases)
  moreover have \<open>sizeC cls \<ge> 1\<close>
    using size_not_0_cls by auto
  ultimately show False 
    using asm by simp
qed

lemma size_1_options_cls: \<open>sizeC cls = 1 \<Longrightarrow> cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp)\<close>
proof (rule ccontr)
  assume asm:\<open>sizeC cls = 1\<close>
  assume \<open>\<not> (cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp))\<close>
  then obtain mat clsI where \<open>cls = Clause (mat # clsI)\<close>
    by (meson nodesCls.cases)
  moreover have \<open>sizeM mat \<ge> 1\<close>
    using size_not_0_mat by auto
  ultimately show False 
    using asm by simp
qed

lemma remove_decrease_size_mat: \<open>sizeM (Matrix (cls # mat)) > sizeM (Matrix mat)\<close> 
proof-
  have \<open>sizeC cls \<ge> 1\<close> 
    using size_not_0_cls by auto
  then show ?thesis 
    by simp
qed

lemma perm_path:
  \<open>ext p2 p1 \<Longrightarrow> pathMat p1 mat \<Longrightarrow> pathMat p2 mat\<close> 
  \<open>ext p2 p1 \<Longrightarrow> pathCls p1 cls \<Longrightarrow> pathCls p2 cls\<close>
proof (induct mat and cls)
  case (LitM x1 x2)
  then show ?case 
    using ext_iff by force
next
  case (Matrix x)
  then show ?case 
    by (meson pathMatQ.simps(2) pathQ_implies_path(1) pathQ_implies_path(2) path_implies_pathQ(1) 
        path_implies_pathQ(2))
next
  case (LitC x1 x2)
  then show ?case 
    using ext_iff by force
next
  case (Clause x)
  then show ?case 
    by (meson pathClsQ.simps(2) pathQ_implies_path(1) pathQ_implies_path(2) path_implies_pathQ(1) 
        path_implies_pathQ(2))
qed

lemma filtered_path:\<open>
  pathMat path mat \<Longrightarrow> 
  (\<And> path'. path' = filter (\<lambda> (pol,prp). containsMat pol prp mat) path \<Longrightarrow>
  pathMat path' mat)\<close> \<open>
  pathCls path cls \<Longrightarrow>
  (\<And> path'. path' = filter (\<lambda> (pol,prp). containsCls pol prp cls) path \<Longrightarrow>
  pathCls path' cls)\<close>
proof (induct mat and cls)
  case (Matrix mat)
  have path_cls:\<open>\<forall> cls \<in> set mat. pathCls path cls\<close> 
    using Matrix.prems(1) pathMatQ.simps(2) pathQ_implies_path(2) path_implies_pathQ(1) by blast
  have \<open>\<forall> cls \<in> set mat. pathClsQ path' cls\<close> 
  proof
    fix cls
    assume asm:\<open>cls \<in> set mat\<close>
    then have 1:\<open>pathCls path cls\<close> 
      by (simp add: path_cls)
    obtain path'' where path''_def:\<open>path'' = filter (\<lambda> (pol,prp). containsCls pol prp cls) path\<close>
      by simp
    have \<open>\<forall> pol prp. (pol,prp) \<in> set path'' \<longrightarrow> (pol,prp) \<in> set path'\<close> 
        using Matrix.prems(2) asm path''_def by auto
    then have \<open>ext path' path''\<close> 
      by (metis ext_iff old.prod.exhaust)
    moreover have \<open>pathCls path'' cls\<close> 
      using path''_def asm 1 Matrix by simp
    ultimately show \<open>pathClsQ path' cls\<close> 
      by (simp add: path_implies_pathQ(2) perm_path(2))
  qed
  then have \<open>pathMatQ path' (Matrix mat)\<close>
    by simp
  then show ?case
    by (simp add: pathQ_implies_path(1))
next
  case (Clause cls)
  then obtain mat where mat_def:\<open>mat \<in> set cls \<and> pathMat path mat\<close>
    using pathClsQ.simps(2) pathQ_implies_path(1) path_implies_pathQ(2) by blast
  then obtain path'' where path''_def:\<open>path'' = filter (\<lambda> (pol,prp). containsMat pol prp mat) path\<close>
    by simp
  have \<open>\<forall> pol prp. (pol,prp) \<in> set path'' \<longrightarrow> (pol,prp) \<in> set path'\<close> 
      using Clause.prems(2) mat_def path''_def by auto
  then have \<open>ext path' path''\<close> 
    by (metis ext_iff old.prod.exhaust)
  moreover have \<open>pathMat path'' mat\<close> 
    using Clause mat_def path''_def by simp
  ultimately show ?case 
    using mat_def pathClsQ.simps(2) pathQ_implies_path(2) path_implies_pathQ(1) perm_path(1) 
    by blast
qed simp_all

lemma exi_path_implies_exi_min_path: 
  \<open>\<exists> path. pathMat path mat \<Longrightarrow> \<exists> path. minPathM path mat\<close>
proof-
  assume \<open>\<exists> path. pathMat path mat\<close>
  then obtain path where path_def:\<open>pathMat path mat\<close> 
    by auto
  obtain path' where path'_def:\<open>path' = filter (\<lambda> (pol,prp). containsMat pol prp mat) path\<close>
    by simp
  then have \<open>pathMat path' mat\<close> 
    using path_def filtered_path by auto
  then have \<open>minPathM path' mat\<close>
    by (simp add: path'_def)
  then show \<open>\<exists> path. minPathM path mat\<close> 
    by auto
qed

theorem path_completeness: \<open>
  \<forall> path'. ext path' Path \<longrightarrow> pathMat path' (Matrix Mat) \<longrightarrow> 
    (\<exists> prp. (False,prp) \<in> set path' \<and> (True,prp) \<in> set path') \<Longrightarrow>
  nanoCoP Mat Path\<close> 
proof (induct \<open>sizeM (Matrix Mat)\<close> arbitrary: Mat Path rule: less_induct)
  case less
  consider \<open>Mat = []\<close> | \<open>\<exists> cls MatI. Mat = cls # MatI\<close>
    by (meson list.exhaust)
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using PathAxiom less.prems by (metis member_iff pathMat.simps(2) perm_iff)
  next
    case 2
    then obtain cls MatI where Mat_def:\<open>Mat = cls # MatI\<close>
      by auto
    consider 
      \<open>\<exists> pol prp. cls = LitC pol prp\<close> | 
      \<open>cls = Clause []\<close> | 
      \<open>\<exists> mat clsI. cls = Clause (mat # clsI)\<close>
      by (meson nodesCls.cases)
    then show ?thesis 
    proof cases
      case 1
      then show ?thesis 
        by (metis ExtensionLitC Mat_def ext.simps(2) less.hyps less.prems pathCls.simps(1) 
            pathMat.simps(3) remove_decrease_size_mat)
    next
      case 2
      then show ?thesis
        by (simp add: Axiom Mat_def)
    next
      case 3
      then obtain mat clsI where cls_def: \<open>cls = Clause (mat # clsI)\<close>
        by auto
      then have rm_mat:\<open>nanoCoP (Clause clsI # MatI) Path\<close> 
      proof-
        have \<open>
          \<forall> p. pathMatQ p (Matrix ((Clause clsI) # MatI)) \<longrightarrow> ext p Path \<longrightarrow>
            pathMatQ p (Matrix Mat)\<close> 
          using cls_def Mat_def by auto
        then have \<open>
          \<forall> p. pathMat p (Matrix ((Clause clsI) # MatI)) \<longrightarrow> ext p Path \<longrightarrow>
            pathMat p (Matrix Mat)\<close> 
          by (metis pathQ_implies_path(1) path_implies_pathQ(1))
        then have \<open>
          \<forall> p. pathMat p (Matrix ((Clause clsI) # MatI)) \<longrightarrow> ext p Path \<longrightarrow> (
          \<exists> prp. (True,prp) \<in> set p \<and> (False,prp) \<in> set p)\<close>
          using less.prems by blast
        moreover have \<open>
          sizeM (Matrix ((Clause clsI) # MatI)) < sizeM (Matrix Mat)\<close>
        proof-
          have \<open>
            sizeM (Matrix Mat) 
            = 2 + sizeM mat + sum (map sizeM clsI) 
              + sum (map sizeC MatI)\<close> 
            using cls_def Mat_def by simp
          moreover have \<open>
            ... > 2 + sum (map sizeM clsI) + 
              sum (map sizeC MatI)\<close> 
            using size_not_0_mat 
            by (metis add_less_cancel_right add_less_le_mono nat_1_add_1 one_less_numeral_iff 
                semiring_norm(76))
          ultimately show ?thesis 
            by simp
        qed
        ultimately show ?thesis 
          using less by fast
      qed
      consider \<open>\<exists> pol prp. mat = LitM pol prp\<close> | \<open>\<exists> matI. mat = Matrix matI\<close>
        by (meson sizeM.cases)
      then show ?thesis 
      proof cases
        case 1
        then obtain pol prp where mat_def: \<open>mat = LitM pol prp\<close>
          by auto
        have \<open>nanoCoP MatI ((pol,prp) # Path)\<close>
          by (simp add: Mat_def cls_def less.hyps less.prems mat_def)
        then show ?thesis
          by (simp add: ExtensionLit Mat_def cls_def mat_def rm_mat)
      next
        case 2
        then obtain matI where mat_def: \<open>mat = Matrix matI\<close> 
          by auto
        have \<open>nanoCoP (matI @ MatI) Path\<close> 
          by (metis Mat_def cls_def less.hyps less.prems list.set_intros(1) mat_def pathCls.simps(3) 
              pathMat.simps(3) pick_mat_size split_matrix_preserves_path unwrap.simps(2))
        then show ?thesis
          by (simp add: ExtensionMat Mat_def cls_def mat_def rm_mat)
      qed
    qed
  qed
qed

(*
  consider 
    (0) \<open>nodesMat (Matrix Mat) = 0\<close> | 
    (1) \<open>nodesMat (Matrix Mat) = 1\<close> | 
    (n) \<open>1 < nodesMat (Matrix Mat)\<close> 
    by linarith
  then show ?case 
  proof cases
    case 0
    have \<open>Mat = []\<close>
    proof (rule ccontr)
      assume "Mat \<noteq> []"
      then obtain hmat tmat where \<open>Mat = hmat # tmat\<close> 
        by (meson list.exhaust)
      then have \<open>nodesMat (Matrix Mat) = 1 + sum (map nodesCls (hmat # tmat))\<close>
        by simp
      then show False 
        by (simp add: "0")
    qed
    then show ?thesis
      using PathAxiom less.prems by (metis member_iff pathMat.simps(2) perm_iff)
  next
    case 1
    then have flat:\<open>\<forall> cls \<in> set Mat. cls = Clause [] \<or> (\<exists> pol prp. cls = LitC pol prp)\<close> 
      using one_node_implies_flat by auto
    have \<open>
      Clause [] \<in> set Mat \<or>
      (\<exists> prp. (True,prp) \<in> set Path \<and> (False,prp) \<in> set Path) \<or>
      (\<exists> prp. LitC True prp \<in> set Mat \<and> LitC False prp \<in> set Mat) \<or>
      (\<exists> pol prp. LitC pol prp \<in> set Mat \<and> (\<not>pol,prp) \<in> set Path)\<close> 
      (is \<open>?empty \<or> ?path \<or> ?mat \<or> ?path_mat\<close>)
    proof (rule ccontr)
      assume asm1:\<open>\<not>(?empty \<or> ?path \<or> ?mat \<or> ?path_mat)\<close>
      then obtain path' where path'_def:\<open>path' = map lit_to_path_elem Mat @ Path\<close>
        by simp
      have path'_iff:\<open>
        \<forall> pol prp. (pol,prp) \<in> set path' \<longleftrightarrow> (pol,prp) \<in> set Path \<or> LitC pol prp \<in> set Mat\<close> 
      proof (rule allI, rule allI, rule iffI)
        fix pol prp
        assume asm2:\<open>(pol,prp) \<in> set path'\<close>
        then consider \<open>(pol,prp) \<in> set Path\<close> | \<open>(pol,prp) \<in> set (map lit_to_path_elem Mat)\<close> 
          using path'_def by auto
        then show \<open>(pol,prp) \<in> set Path \<or> LitC pol prp \<in> set Mat\<close>
        proof cases
          case 1
          then show ?thesis
            by simp
        next
          case 2
          then obtain cls where cls_def: \<open>cls \<in> set Mat \<and> (pol,prp) = lit_to_path_elem cls\<close> 
            by auto
          then show ?thesis
            using flat asm1 by (metis Pair_inject lit_to_path_elem.simps(1))
        qed
      next
        fix pol prp
        assume asm2:\<open>(pol,prp) \<in> set Path \<or> LitC pol prp \<in> set Mat\<close>
        then show \<open>(pol,prp) \<in> set path'\<close> 
            using path'_def by force
      qed
      then have \<open>\<nexists> prp. (True,prp) \<in> set path' \<and> (False,prp) \<in> set path'\<close> 
        by (metis (full_types) asm1)
      moreover have \<open>ext path' Path\<close>  
        by (simp add: ext_iff path'_def)
      moreover have \<open>pathMat path' (Matrix Mat)\<close> 
      proof-
        have \<open>pathMatQ path' (Matrix Mat)\<close> 
          using asm1 flat path'_iff by auto
        then show ?thesis 
          using pathQ_implies_path(1) by blast
      qed
      ultimately show False
        by (meson less.prems)
    qed
    then consider 
      \<open>Clause [] \<in> set Mat\<close> |
      \<open>\<exists> prp. (True,prp) \<in> set Path \<and> (False,prp) \<in> set Path\<close> |
      \<open>\<exists> prp. LitC True prp \<in> set Mat \<and> LitC False prp \<in> set Mat\<close> |
      \<open>\<exists> pol prp. LitC pol prp \<in> set Mat \<and> (\<not>pol,prp) \<in> set Path\<close> 
      by fast
    then show ?thesis 
    proof cases
      case 1
      then show ?thesis 
        by (metis Axiom ExtMat move_to_front_perm)
    next
      case 2
      then show ?thesis 
        using PathAxiom by fastforce
    next
      case 3
      then show ?thesis 
        by (smt (verit) ExtensionLitC ExtMat ReductionLitC ext.simps(2) member_iff perm_iff)
    next
      case 4
      then show ?thesis
        by (metis (full_types) ExtMat ReductionLitC ext.simps(2) member_iff perm_iff)
    qed
  next
    case n
    consider \<open>\<nexists> path. pathMat path (Matrix Mat)\<close> | \<open>\<exists> path. pathMat path (Matrix Mat)\<close> 
      by auto
    then show ?thesis 
    proof cases
      case 1
      then have \<open>\<nexists> path. pathMatQ path (Matrix Mat)\<close> 
        using pathQ_implies_path(1) by blast
      obtain cls where cls_def: \<open>cls \<in> set Mat \<and> (\<nexists> path. pathCls path cls)\<close>  
        by (meson "1" cls_path_gives_mat_path)
      then consider 
        \<open>\<exists> pol prp. cls = LitC pol prp\<close> | 
        \<open>cls = Clause []\<close> | 
        \<open>\<exists> hcls tcls. cls = Clause (hcls # tcls)\<close> 
        by (meson nodesCls.cases)
      then have \<open>nanoCoP (cls # Mat) Path\<close> 
      proof cases
        case 1
        then show ?thesis
          by (metis cls_def nanoCoP2.member.simps(2) pathCls.simps(1))
      next
        case 2
        then show ?thesis
          by (simp add: Axiom)
      next
        case 3
        then obtain hcls tcls where hcls_def:\<open>cls = Clause (hcls # tcls)\<close> 
          by auto
        consider \<open>\<exists> pol prp. hcls = LitM pol prp\<close> | \<open>\<exists> mat. hcls = Matrix mat\<close> 
          by (meson clause_elem.exhaust)
        then show ?thesis 
        proof cases
          case 1
          then show ?thesis
            by (metis hcls_def cls_def nanoCoP2.member.simps(2) 
                pathCls.simps(3) pathMat.simps(1))
        next
          case 2
          then obtain mat where mat_def:\<open>hcls = Matrix mat\<close>
            by auto
          have \<open>nanoCoP (mat @ remove1 cls Mat) Path\<close> 
            by (metis cls_def hcls_def less.hyps list.set_intros(1) mat_def pathCls.simps(3) 
                pick_mat_size shuffle_size_mat split_matrix_preserves_path unwrap.simps(2))
          moreover have \<open>nanoCoP (Clause tcls # remove1 cls Mat) Path\<close> 
          proof-
            have \<open>sizeM (Matrix Mat) = sizeM (Matrix (cls # remove1 cls Mat))\<close> 
              using cls_def shuffle_size_mat by fastforce
            moreover have \<open>
              ... = 
              1 + sizeC (Clause ((Matrix mat) # tcls)) + sum (map sizeC (remove1 cls Mat))\<close>
              using hcls_def mat_def by simp
            moreover have \<open>
              sizeC (Clause ((Matrix mat) # tcls)) > sizeC (Clause tcls)\<close>
              by simp
            ultimately have 
              \<open>sizeM (Matrix (Clause tcls # remove1 cls Mat)) < sizeM (Matrix Mat)\<close> 
              by simp
            moreover  have \<open>\<nexists> path. pathMat path (Matrix (Clause tcls # remove1 cls Mat))\<close>
                using "1" pathMat.simps(3) cls_def hcls_def by auto
            ultimately show ?thesis 
              using less.hyps by blast
          qed
          ultimately have \<open>nanoCoP (cls # remove1 cls Mat) Path\<close> 
            using ExtensionMat hcls_def mat_def by auto
          then show ?thesis 
            by (metis ExtMat cls_def ext.simps(2) move_to_front_perm perm_iff)
        qed
      qed
      then show ?thesis
        by (metis ExtMat cls_def ext.simps(2)  move_to_front_perm perm_iff)
    next
      case 2
      then obtain path where path_def:\<open>minPathM path (Matrix Mat)\<close>
        using exi_path_implies_exi_min_path by blast
      then obtain path' where path'_def: \<open>path' = Path @ path\<close> 
        by simp
      then have ext_path'_Path: \<open>ext path' Path\<close>  
        using ext_iff by fastforce
      have path'Mat: \<open>pathMat path' (Matrix Mat)\<close> 
        using path_def path'_def prefixPath(1) by blast
      obtain prp where prp_def:\<open>(True,prp) \<in> set path' \<and> (False,prp) \<in> set path'\<close>
        using ext_path'_Path less.prems path'Mat by auto
      then consider 
        \<open>(True,prp) \<in> set Path \<and> (False,prp) \<in> set Path\<close> |
        \<open>\<exists> pol. (pol,prp) \<in> set Path \<and> (\<not>pol,prp) \<in> set path\<close> |
        \<open>(True,prp) \<in> set path \<and> (False,prp) \<in> set path\<close> 
        using path'_def by fastforce
      then show ?thesis 
      proof cases
        case 1
        then show ?thesis
          using PathAxiom by fastforce
      next
        case 2
        then obtain pol where comp_def:\<open>(pol,prp) \<in> set Path \<and> (\<not>pol,prp) \<in> set path\<close>
          by auto
        then have \<open>containsMat (\<not>pol) prp (Matrix Mat)\<close> 
          using path_def by auto
        then obtain cls where cls_def:\<open>cls \<in> set Mat \<and> containsCls (\<not>pol) prp cls\<close>
          by (meson containsMat.simps(2))
        consider 
          (found)\<open>cls = LitC (\<not>pol) prp\<close> | 
          (notFound)\<open>\<exists> mat clsI. cls = Clause clsI \<and> mat \<in> set clsI \<and> containsMat (\<not>pol) prp mat\<close> 
          by (smt (z3) cls_def containsCls.elims(1))
        then have "nanoCoP (cls # remove1 cls Mat) Path"
        proof cases
          case found
          then show ?thesis
            by (simp add: ReductionLitC local.comp_def)
        next
          case notFound
          then obtain clsI mat where clsI_def:\<open>
            cls = Clause clsI \<and> mat \<in> set clsI \<and> containsMat (\<not>pol) prp mat\<close>
            by auto
          have rm_mat:\<open>nanoCoP ((Clause (remove1 mat clsI)) # remove1 cls Mat) Path\<close> 
          proof-
            have \<open>
              \<forall> p. pathMatQ p (Matrix ((Clause (remove1 mat clsI)) # remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow>
                pathMatQ p (Matrix Mat)\<close> 
              using cls_def clsI_def 
              by (metis move_to_front_perm pathCls.simps(3) pathMat.simps(3) pathQ_implies_path(1) 
                  path_implies_pathQ(1) permPath(1) permPath(2) )
            then have \<open>
              \<forall> p. pathMat p (Matrix ((Clause (remove1 mat clsI)) # remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow>
                pathMat p (Matrix Mat)\<close> 
              by (metis pathQ_implies_path(1) path_implies_pathQ(1))
            then have \<open>
              \<forall> p. pathMat p (Matrix ((Clause (remove1 mat clsI)) # remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow> (
              \<exists> prp. (True,prp) \<in> set p \<and> (False,prp) \<in> set p)\<close>
              using less.prems by blast
            moreover have \<open>
              sizeM (Matrix ((Clause (remove1 mat clsI)) # remove1 cls Mat)) < sizeM (Matrix Mat)\<close> 
            proof-
              have \<open>
                sizeM (Matrix Mat) 
                = 2 + sizeM mat + sum (map sizeM (remove1 mat clsI)) 
                  + sum (map sizeC (remove1 cls Mat))\<close> 
                using cls_def shuffle_size_mat clsI_def shuffle_size_cls by fastforce
              moreover have \<open>
                ... > 2 + sum (map sizeM (remove1 mat clsI)) + 
                  sum (map sizeC (remove1 cls Mat))\<close> 
                by (metis add_strict_right_mono less_Suc_eq_0_disj less_add_same_cancel1 
                    plus_1_eq_Suc sizeM.elims)
              ultimately show ?thesis 
                by simp
            qed
            ultimately show ?thesis 
              by (meson less.hyps)
          qed
          have \<open>\<forall> pol' prp'. mat = LitM pol' prp' \<longrightarrow> pol' = (\<not>pol) \<and> prp' = prp\<close> 
            using clsI_def by auto
          then consider (found')\<open>mat = LitM (\<not>pol) prp\<close> | (notFound')\<open>\<exists> matI. mat = Matrix matI\<close>
            by (smt (verit, del_insts) sizeM.cases) 
          then have \<open>nanoCoP ((Clause (mat # remove1 mat clsI)) # remove1 cls Mat) Path\<close>
          proof cases
            case found'
            then show ?thesis 
              using rm_mat ReductionLit local.comp_def member_iff by fastforce 
          next
            case notFound'
            then obtain matI where matI_def:\<open>mat = Matrix matI\<close> 
              by auto
            then have \<open>nanoCoP (matI @ remove1 cls Mat) Path\<close>
            proof-
              have \<open>
                \<forall> p. pathMatQ p (Matrix (matI @ remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow>
                  pathMatQ p (Matrix Mat)\<close> 
                using matI_def cls_def clsI_def 
                by (metis move_to_front_perm pathCls.simps(3) pathMat.simps(3) pathQ_implies_path(1) 
                    path_implies_pathQ(1) permPath(1) permPath(2) split_matrix_preserves_path)
              then have \<open>
                \<forall> p. pathMat p (Matrix (matI @ remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow>
                  pathMat p (Matrix Mat)\<close> 
                by (metis pathQ_implies_path(1) path_implies_pathQ(1))
              then have \<open>
                \<forall> p. pathMat p (Matrix (matI @ remove1 cls Mat)) \<longrightarrow> ext p Path \<longrightarrow> (
                \<exists> prp. (True,prp) \<in> set p \<and> (False,prp) \<in> set p)\<close>
                using less.prems by blast
              moreover have \<open>
                sizeM (Matrix (matI @ remove1 cls Mat)) < sizeM (Matrix Mat)\<close> 
                using matI_def cls_def 
                by (metis clsI_def pick_mat_size shuffle_size_mat unwrap.simps(2))
              ultimately show ?thesis 
                by (meson less.hyps)
            qed
            then show ?thesis 
              using ExtensionMat matI_def rm_mat by auto
          qed
          then show ?thesis 
            by (metis ExtCls clsI_def move_to_front_perm)
        qed
        then show ?thesis 
          by (meson ExtMat cls_def move_to_front_perm)
      next
        case 3
        then have \<open>containsMat True prp (Matrix Mat)\<close> 
          using path_def by auto
        then obtain cls where \<open>cls \<in> set Mat \<and> containsCls True prp cls\<close> 
          by auto
        have \<open>nanoCoP (cls # remove1 cls Mat) Path\<close>
        then show ?thesis sorry
      qed
    qed
  qed
qed*)

theorem completeness: \<open>
  \<forall> i. semanticsMat i (Matrix mat) \<Longrightarrow> nanoCoP mat []\<close>
  by (simp add: path_completeness syntactic_to_semantic_validity)

theorem main: \<open>nanoCoP mat [] \<longleftrightarrow> (\<forall> i. semanticsMat i (Matrix mat))\<close> 
  using completeness soundness by auto

end