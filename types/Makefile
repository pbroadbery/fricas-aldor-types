
SUBDIRS = index

define dep_template
files_$i := $(shell ls *.as)
endef

$(foreach l,$(ALDOR_FILES), $(eval $(call dep_template,$(l))))

include buildmodule.mk

---

FILES := a b c
a_deps := ...