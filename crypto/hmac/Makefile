# FStar variables
FSTAR_HOME?=../../../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe

# Libraries
LIB_DIR_HST=../../lib/hst
LIB_FILES_HST= Math.Axioms.fst Math.Lib.fst Math.Lemmas.fst Math.Logic.Axioms.fst Hacl.UInt8.fst Hacl.UInt16.fst Hacl.UInt32.fst Hacl.UInt64.fst Hacl.UInt128.fst Hacl.SBuffer.fst Hacl.Cast.fst

# Utils 
UTILS_DIR_HST=../utils
UTILS_FILES_HST= Hacl.Operations.fst Hacl.Operations.Pure.fst Hacl.Conversions.fst


# Dependencies
SHA2_256_DIR=../hash
SHA2_256_HST=Hash.SHA2.L256.fst
SHA2_256_PURE_HST=Hash.SHA2.L256.Pure.fst
SHA2_256_MASKED_HST=Hash.SHA2.L256.Masked.fst


.PHONY: prepare lax ver clean

all: lax

prepare:
	cp $(LIB_DIR_HST)/*.fst .
	cp $(addprefix $(UTILS_DIR_HST)/, $(UTILS_FILES_HST)) .
	cp $(SHA2_256_DIR)/$(SHA2_256_HST) .
	cp $(SHA2_256_DIR)/$(SHA2_256_PURE_HST) .
	cp $(SHA2_256_DIR)/$(SHA2_256_MASKED_HST) .

lax: prepare
	$(FSTAR) --lax HMAC.fst
	$(FSTAR) --lax HMAC.B.fst
	$(FSTAR) --lax HMAC.Pure.fst
	$(FSTAR) --lax HMAC.Masked.fst

ver:
	$(FSTAR) HMAC.fst
	$(FSTAR) HMAC.B.fst
	$(FSTAR) HMAC.Pure.fst
	$(FSTAR) HMAC.Masked.fst

clean:
	rm -f *~ $(LIB_FILES_HST) $(UTILS_FILES_HST) $(SHA2_256_HST)

