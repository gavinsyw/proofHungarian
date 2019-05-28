CURRENT_DIR = "./"
-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = lib graph
INCLUDE_RAMIFYCOQ = $(foreach d, $(DIRS), -Q $(d) RamifyCoq.$(d)) -Q "." RamifyCoq
NORMAL_FLAG = $(INCLUDE_RAMIFYCOQ)

LIB_FILES = \
  Coqlib.v Equivalence_ext.v List_Func_ext.v Ensembles_ext.v List_ext.v EnumEnsembles.v Relation_ext.v relation_list.v EquivDec_ext.v Morphisms_ext.v StrongInduction.v

GRAPH_FILES = \
  graph_model.v path_lemmas.v find_not_in.v reachable_ind.v

NORMAL_FILES = \
  $(GRAPH_FILES:%.v=graph/%.v) \
  $(LIB_FILES:%.v=lib/%.v)

$(NORMAL_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(NORMAL_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(NORMAL_FILES:%.v=%.vo)

depend:
	@$(COQDEP) $(NORMAL_FLAG) $(NORMAL_FILES) > .depend

clean:
	@rm */*.vo */*.glob */.*.aux

.DEFAULT_GOAL := all

include .depend
