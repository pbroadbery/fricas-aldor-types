
all-ao: $(addsuffix .ao, $(ALDOR_FILES))
all-tests: $(addsuffix .ao, $(TEST_FILES))

define rec_dep_template
$(foreach l, $($1_deps), $(call rec_dep_template,$(l))) $(l)
endef

uniq_0 = $(if $1,$(firstword $1) $(call uniq,$(filter-out $(firstword $1),$1)))
uniq = $(call uniq_0,$1)
uniq_deps = $(call uniq,$(call rec_dep_template,$1))

$(addsuffix .ao, $(ALDOR_FILES)): %.ao: %.as
	echo dependencies $(call uniq_deps,$*)
	ar r lib$(LIB_NAME)_$*.al $(addsuffix .ao, $(call uniq_deps,$*))
	$(ALDOR_$(X)) $(LOG_FLAGS) $(OPT_FLAGS) -Fabn -Fao -ffm -Y. -l$(LIB_NAME)Lib=$(LIB_NAME)_$* $< $(LOG_$(X))

$(addsuffix .gloop, $(ALDOR_FILES)): %.gloop: %.gloop
	ar r lib$(LIB_NAME)_$*.al $(addsuffix .ao, $(call uniq_deps,$*))
	$(ALDOR_$(X)) $(LOG_FLAGS) $(OPT_FLAGS) -Y. -l$(LIB_NAME)Lib=$(LIB_NAME)_$* -gloop

$(addsuffix .o, $(ALDOR_FILES)): %.o: %.ao
	$(ALDOR_$(X)) $(LOG_FLAGS) $(OPT_FLAGS) -fo $*.ao

$(addsuffix .ao, $(TEST_FILES)): %.ao: lib$(LIB_NAME).al %.as
	$(ALDOR_$(X)) $(LOG_FLAGS) $(OPT_FLAGS) -Fabn -Fao -Y. -l$(LIB_NAME) $*.as $(LOG_$(X))

lib$(LIB_NAME).al: $(addsuffix .ao, $(ALDOR_FILES))
	ar r lib$(LIB_NAME).al $(addsuffix .ao,$(call uniq,$(foreach i,$(ALDOR_FILES),$(call uniq_deps,$i) $i)))

lib$(LIB_NAME).a: $(addsuffix .o, $(ALDOR_FILES))
	ar r lib$(LIB_NAME).a $(addsuffix .o,$(call uniq,$(foreach i,$(ALDOR_FILES),$(call uniq_deps,$i) $i)))

$(addsuffix .abn, $(ALDOR_FILES)) $(addsuffix .abn, $(TEST_FILES)): %.abn: %.ao
	echo "hello"

.PHONY: $(addsuffix .run, $(ALDOR_FILES))

$(addsuffix .run, $(ALDOR_FILES)): %.run: %.ao
	$(ALDOR_$(X)) -laldor -ginterp $*

$(addsuffix .exe, $(ALDOR_FILES)): %.exe: %.ao
	rm -f $@
	$(ALDOR_$(X)) -laldor -lalgebra -fx=$@ -Zdb $< $(addsuffix .ao, $(call uniq_deps,$*))

$(addsuffix .exe, $(TEST_FILES)): %.exe: %.ao lib$(LIB_NAME).a
	rm -f $@
	$(ALDOR_$(X)) -fx=$@ -Zdb -l$(LIB_NAME) -lalgebra -laldor $*.ao

define dep_template
$1.ao: $(addsuffix .ao,$($1_deps))
endef

$(foreach l,$(ALDOR_FILES), $(eval $(call dep_template,$(l))))

clean:
	rm -f *.ao *.abn *.c *.fm *.al

# Used to extract file information
idea:
	echo run: $(addsuffix .run, $(ALDOR_FILES))
	echo files: $(addsuffix .as, $(ALDOR_FILES))

