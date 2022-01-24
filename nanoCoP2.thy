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
  = Lit "bool" 'a
  | Matrix "'a matrix_elem list"
and ('a) matrix_elem
  = Clause \<open>'a clause_elem list\<close>

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
  Axiom: \<open>nanoCoP (Clause [] # Mat) Path\<close> |
  PermMat: \<open>nanoCoP Mat2 Path\<close> if \<open>nanoCoP Mat1 Path\<close> and \<open>perm Mat1 Mat2\<close> |
  PermCls: \<open>nanoCoP (Clause Cls2 # Mat) Path\<close> if 
    \<open>perm Cls1 Cls2\<close> and \<open>nanoCoP (Clause Cls1 # Mat) Path\<close> |
  ReductionLit: \<open>nanoCoP (Clause (Lit pol prp # Cls) # Mat) Path\<close> if
    \<open>member (\<not>pol, prp) Path\<close> and \<open>nanoCoP (Clause Cls # Mat) Path\<close> |
  ReductionMat: \<open>
    nanoCoP mat Path \<Longrightarrow>
    nanoCoP (Clause Cls # Mat) Path \<Longrightarrow>
      nanoCoP (Clause (Matrix mat # Cls) # Mat) Path\<close> |
  ExtensionLit: \<open>
    nanoCoP Mat ((pol, prp) # Path) \<Longrightarrow> 
    nanoCoP (Clause Cls # Mat) Path \<Longrightarrow>
      nanoCoP (Clause (Lit pol prp # Cls) # Mat) Path\<close> |
  ExtensionMat: \<open>
    nanoCoP (Clause [Matrix mat] # Mat) Path \<Longrightarrow> 
    nanoCoP (Clause Cls # Mat) Path \<Longrightarrow>
      nanoCoP (Clause (Matrix mat # Cls) # Mat) Path\<close>

(*Example proofs*)
context begin
private datatype props = P | Q | R

(*Way more steps are required than in the original
Part of this is because of the replacement with beta-clauses, which is a permissible rule*)
private lemma \<open>nanoCoP 
  [
    Clause [Lit False P],
    Clause [
      Matrix [Clause [Lit True P],Clause [Lit False Q]],
      Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
    ],
    Clause [Lit True Q]
  ] 
  []\<close>
proof-
  from ExtensionLit have ?thesis if \<open>nanoCoP 
    [
      Clause [
        Matrix [Clause [Lit True P],Clause [Lit False Q]],
        Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
      ],
      Clause [Lit True Q]
    ] 
  [(False, P)]\<close> and \<open>nanoCoP 
    [
      Clause [],
      Clause [
        Matrix [Clause [Lit True P],Clause [Lit False Q]],
        Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
      ],
      Clause [Lit True Q]
    ] 
  []\<close> using that by fast
  with Axiom have ?thesis if \<open>nanoCoP 
    [
      Clause [
        Matrix [Clause [Lit True P],Clause [Lit False Q]],
        Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
      ],
      Clause [Lit True Q]
    ] 
  [(False, P)]\<close> using that by fast
  with ReductionMat have ?thesis if \<open>nanoCoP
    [Clause [Lit True P],Clause [Lit False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [
        Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
      ],
      Clause [Lit True Q]
    ] 
  [(False, P)]\<close> using that by fast
  with ReductionMat have ?thesis if \<open>nanoCoP
    [Clause [Lit True P],Clause [Lit False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
  [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [Lit True Q]]
  [(False, P)]\<close> using that by fast 
  with ReductionLit have ?thesis if \<open>nanoCoP
    [
      Clause [],
      Clause [Lit False Q]]
    [(False, P)]\<close> and \<open>nanoCoP
  [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
    [(False, P)]\<close> and \<open>nanoCoP
    [
      Clause [],
      Clause [Lit True Q]]
  [(False, P)]\<close> using that by force
  with Axiom have ?thesis if \<open>nanoCoP
    [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
  [(False, P)]\<close> using that by fast
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [Lit False Q,Lit True R],Clause [Lit False R]]
  [(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
  [(False, P)]\<close> using that by fast
  with Axiom have ?thesis if \<open>nanoCoP
    [Clause [Lit False Q,Lit True R],Clause [Lit False R]]
  [(True, Q),(False, P)]\<close> using that by fast
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause [Lit True R],Clause [Lit False R]]
  [(True, Q),(False, P)]\<close> using that member.simps(2) by (metis (full_types))
  with ExtensionLit have ?thesis if \<open>nanoCoP
    [Clause [Lit False R]]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [Lit False R]]
  [(True, Q),(False, P)]\<close> using that by fastforce
  with ReductionLit have ?thesis if \<open>nanoCoP
    [Clause []]
  [(True, R),(True, Q),(False, P)]\<close> and \<open>nanoCoP
    [Clause [],Clause [Lit False R]]
  [(True, Q), (False, P)]\<close> using that member.simps(2) by (metis (full_types))
  with Axiom show ?thesis by fast
qed

(*could also be done with sledgehammer:*)
private lemma \<open>nanoCoP 
  [
    Clause [Lit False P],
    Clause [
      Matrix [Clause [Lit True P],Clause [Lit False Q]],
      Matrix [Clause [Lit True Q],Clause [Lit False Q,Lit True R],Clause [Lit False R]]
    ],
    Clause [Lit True Q]
  ] 
  []\<close> 
  by (simp add: Axiom ExtensionLit ReductionLit ReductionMat)
end

abbreviation \<open>evalLit i pol prp \<equiv> ((pol \<and> \<not>i prp) \<or> (\<not>pol \<and> i prp))\<close>

fun semanticsClsElem semanticsMatElem where
  \<open>semanticsClsElem i (Lit pol prp) = evalLit i pol prp\<close> | 
  \<open>semanticsClsElem i (Matrix []) = False\<close> |
  \<open>semanticsClsElem i (Matrix (cls # mat)) = 
    (semanticsMatElem i cls \<or> semanticsClsElem i (Matrix mat))\<close> |
  \<open>semanticsMatElem i (Clause []) = True\<close> |
  \<open>semanticsMatElem i (Clause (mat # cls)) = 
    (semanticsClsElem i mat \<and> semanticsMatElem i (Clause cls))\<close>  

fun pathClsElem pathMatElem where
  \<open>pathClsElem path (Lit pol prp) = member (pol,prp) path\<close> | 
  \<open>pathClsElem path (Matrix []) = True\<close> | 
  \<open>pathClsElem path (Matrix (cls # mat)) = (pathMatElem path cls \<and> pathClsElem path (Matrix mat))\<close> | 
  \<open>pathMatElem path (Clause []) = False\<close> |
  \<open>pathMatElem path (Clause (mat # cls)) = (pathClsElem path mat \<or> pathMatElem path (Clause cls))\<close> 

(*Weird equality thing needed to get induction correct*)
lemma prefixPath: 
  \<open>pathClsElem path mat \<Longrightarrow> path' = (prefix @ path) \<Longrightarrow> pathClsElem path' mat\<close>
  \<open>pathMatElem path cls \<Longrightarrow> path' = (prefix @ path) \<Longrightarrow> pathMatElem path' cls\<close>
  by (induct mat and cls rule: pathClsElem_pathMatElem.induct) auto

lemma suffixPath: 
  \<open>pathClsElem path mat \<Longrightarrow> path' = (path @ suffix) \<Longrightarrow> pathClsElem path' mat\<close>
  \<open>pathMatElem path cls \<Longrightarrow> path' = (path @ suffix) \<Longrightarrow> pathMatElem path' cls\<close>
  by (induct mat and cls rule: pathClsElem_pathMatElem.induct) auto+

(* Quantifier semantics:*)
fun semanticsMatQ semanticsClsQ where
  \<open>semanticsMatQ i (Lit pol prp) = evalLit i pol prp\<close> |
  \<open>semanticsMatQ i (Matrix mat) = (\<exists> cls \<in> set mat. semanticsClsQ i cls)\<close> |
  \<open>semanticsClsQ i (Clause cls) = (\<forall> cls_elem \<in> set cls. semanticsMatQ i cls_elem)\<close> 

lemma semantics_implies_semanticsQ:
  \<open>semanticsClsElem i mat \<Longrightarrow> semanticsMatQ i mat\<close>
  \<open>semanticsMatElem i cls \<Longrightarrow> semanticsClsQ i cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp

lemma semanticsQ_implies_semantics:
  \<open>semanticsMatQ i mat \<Longrightarrow> semanticsClsElem i mat\<close>
  \<open>semanticsClsQ i cls \<Longrightarrow> semanticsMatElem i cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp

fun pathMatQ pathClsQ where
  \<open>pathMatQ path (Lit pol prp) = member (pol, prp) path\<close> | 
  \<open>pathMatQ path (Matrix mat) = (\<forall> cls \<in> set mat. pathClsQ path cls)\<close> | 
  \<open>pathClsQ path (Clause cls) = (\<exists> cls_elem \<in> set cls. pathMatQ path cls_elem)\<close> 

lemma path_implies_pathQ:
  \<open>pathClsElem path mat \<Longrightarrow> pathMatQ path mat\<close>
  \<open>pathMatElem path cls \<Longrightarrow> pathClsQ path cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp

lemma pathQ_implies_path:
  \<open>pathMatQ path mat \<Longrightarrow> pathClsElem path mat\<close>
  \<open>pathClsQ path cls \<Longrightarrow> pathMatElem path cls\<close>
proof (induct mat and cls)
  case (Matrix x)
  then show ?case 
    by (induct x) auto
next
  case (Clause x)
  then show ?case 
    by (induct x) auto
qed simp

lemma tbd:\<open>
  \<exists> prp. member (True, prp) path \<and> member (False,prp) path \<Longrightarrow>
    \<forall> i. \<exists> (pol,prp) \<in> set path. evalLit i pol prp\<close>
  by (metis (no_types, lifting) case_prodI member_iff)


lemma p1:\<open>
  pathMatElem path cls \<Longrightarrow> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path) \<Longrightarrow>
    \<exists> i. \<not>semanticsMatElem i cls\<close> sorry

lemma p2:\<open>
  pathClsElem path mat \<Longrightarrow> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path) \<Longrightarrow>
    \<exists> i. \<not>semanticsClsElem i mat\<close> sorry

lemma p3:\<open>
  \<not>semanticsMatElem i cls \<Longrightarrow> 
  (\<exists> path. pathMatElem path cls \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> sorry

lemma p4:\<open>
  \<not>semanticsClsElem i mat \<Longrightarrow> 
  (\<exists> path. pathClsElem path mat \<and> \<not>(\<exists> prp. (False,prp) \<in> set path \<and> (True, prp) \<in> set path))\<close> sorry

lemma \<open>
  (\<forall> path. pathClsElem path mat \<longrightarrow> (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)) \<longleftrightarrow>
    (\<forall> i. semanticsClsElem i mat)\<close> 
  by (meson p2 p4)

lemma \<open>
  (\<forall> path. pathMatElem path mat \<longrightarrow> (\<exists> prp. (False,prp) \<in> set path \<and> (True,prp) \<in> set path)) \<longleftrightarrow>
    (\<forall> i. semanticsMatElem i mat)\<close> 
  by (meson p1 p3)


lemma permPath: 
  \<open>pathClsElem path mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow> 
    pathClsElem path matb\<close>
  \<open>pathMatElem path clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    pathMatElem path clsb\<close>
proof (induct mata and clsa)
  case (Matrix x)
  then show ?case 
    by (metis pathMatQ.simps(2) pathQ_implies_path(1) path_implies_pathQ(1) perm_iff)
next
  case (Clause x)
  then show ?case
    by (metis pathClsQ.simps pathQ_implies_path(2) path_implies_pathQ(2) perm_iff)
qed auto

lemma permSemantics:
  \<open>semanticsClsElem i mata \<Longrightarrow> mata = Matrix mat1 \<Longrightarrow> matb = Matrix mat2 \<Longrightarrow> perm mat1 mat2 \<Longrightarrow>
    semanticsClsElem i matb\<close>
  \<open>semanticsMatElem i clsa \<Longrightarrow> clsa = Clause cls1 \<Longrightarrow> clsb = Clause cls2 \<Longrightarrow> perm cls1 cls2 \<Longrightarrow>
    semanticsMatElem i clsb\<close>
proof (induct mata and clsa)
  case (Matrix x)
  then show ?case 
    by (metis perm_iff semanticsMatQ.simps(2) semanticsQ_implies_semantics(1) 
        semantics_implies_semanticsQ(1))
next
  case (Clause x)
  then show ?case
    by (metis perm_iff semanticsClsQ.simps semanticsQ_implies_semantics(2) 
        semantics_implies_semanticsQ(2))
qed auto

theorem path_soundness: 
  \<open>nanoCoP mat path \<Longrightarrow> \<forall> path'. ext path' path \<longrightarrow> pathClsElem path' (Matrix mat) \<longrightarrow> 
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
    by (meson pathClsElem.simps(3) permPath(2))
next
  case (ReductionLit pol prp Path Cls Mat)
  then show ?case 
    by (smt (verit, best) ext_iff member_iff pathClsElem.simps(1) pathClsElem.simps(3) 
        pathMatElem.simps(2))
next
  case (ReductionMat mat Path Cls Mat)
  then show ?case 
    by auto
next
  case (ExtensionLit Mat pol prp Path Cls)
  then show ?case
    by (metis ext.simps(2) pathClsElem.simps(1) pathClsElem.simps(3) pathMatElem.simps(2))
next
  case (ExtensionMat mat Mat Path Cls)
  then show ?case
    by auto
qed

theorem soundness: \<open>nanoCoP mat [] \<Longrightarrow> (\<forall> i. semanticsClsElem i (Matrix mat))\<close> 
  by (meson ext.simps(1) p4 path_soundness)

theorem main: \<open>nanoCoP mat [] \<longleftrightarrow> (\<forall> i. semanticsMat i mat)\<close> sorry

end