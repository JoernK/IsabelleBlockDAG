# IsabelleBlockDAG
Isabelle/Isar library to formally model blockDAG consensus rankings (as a generalization of Nakamoto longest chain rule).
Based on [Isabelle/HOL](https://isabelle.in.tum.de/dist/library/HOL/index.html) and Noschinski's [Graph Theory](https://www.isa-afp.org/entries/Graph_Theory.html) [[Nos16]](https://doi.org/10.1007/s11786-014-0183-z).

The repository is structured as follows:

   
  * `ROOT`
    Isabelle Session ROOT file for IsabelleBlockDAG
    
**Main** blockDAG Theory files:
  
   * `DAGs.thy`
    Model of (finite) directed acyclic graphs (DAGs) as restricted `digraph`s (Graph Theory). 
    Includes helpful definitions/operations on graphs (and corresponding lemmas) including `past_nodes`, `future_nodes`, `cone`, `anticone`, `tips` and `reduce_past`. 
    
  * `blockDAG.thy`
    BlockDAG graph model including (many needed) lemmas about the *genesis* node, reduction (*reduce_past*) of blockDAGs and *induction* for blockDAGs.
    
  * `Extend_blockDAG.thy`
    Definition and lemmas for *appending* relations between graphs.
  
  * `Properties.thy`
    Definition of our (blockDAG/tournament) properties *linearity*, *topology_preserving* and *one-appending monotonicity* and *one-appending robustness*.


**Implementation / Verification** of **SPECTRE** and **GHOSTDAG**:

  * `Spectre.thy`
    Implementation and soundness/terminations proofs for **SPECTRE**[[SLZ16]](http://eprint.iacr.org/2016/1159). 
    
  * `Spectre_Properties.thy`
    Proofs of *topology_preserving*, *one-appending monotonicity* and *one-appending robustness* properties of **SPECTRE**


  * `Ghostdag.thy`
    Implementation and soundness/terminations proofs for **GHOSTDAG**[[SWZ21]](https://doi.org/10.1145/3479722.3480990). 
    
  * `Ghostdag_Properties.thy`
    Proofs of *linearity*, *topology_preserving* and *one-appending monotonicity* properties of **GHOSTDAG**
    

**Helper Theories**:
  
 
  * `DigraphUtils.thy`
    Helpfull lemmas extending Noschinski's Graph Theory.
  * `TopSort.thy`
    Topologic Sorting implementation (variation of insertion sort) needed as **GHOSTDAG** helper function.
  
  * `TopSortD.thy`
    (OLD) Alternative Topologic Sorting implementation.
    
  * `Utils.thy`
    Currently consists of helper functions and lemmas used for **GHOSTDAG**.
    
  * `Verts_To_List.thy`
    Other topological sorting approach based on *unfolding* graph nodes. 
  
**Experimental / Ongoing Work**: 
  
  * `Compostition.thy`
    Models compositions of blockDAGs (i.e., blockDAGs where the nodes are again blockDAGs) 

  * `SpectreComposition.thy`
    Extension of Spectre to *graphs of graphs* as defined in `Composition.thy`. 
  
  * `blockDAG_Type.thy`
    Utilizes `blockDAG.thy` to model blockDAGs as Isabelle *type_def* (and not only *locale*). 
    Also consists of lemmas to improve **SPECTRE** implementation performance (including code lemmas). 
 
**Code Generation**:
  
 * `Codegen.thy`
    Needed lemmas for code exportation and implementation of contradicting examples for the *linearity* of SPECTRE and *one-appending robustness* of GHOSTDAG.
    
 * `code/`
    Contains all exported Haskell code and a Test.hs file with predefined blockDAGs.
  
**Documentation** (A *full* documentation can be found [here](document/document.pdf)):

  * `document/`
    Contains the root.tex file used for the auto-generated IsabelleBlockDAG documentation.
  
  * `output/`
    Contains the auto-generated IsabelleBlockDAG documentations (and corresponding .tex files). 


    
