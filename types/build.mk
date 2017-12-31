all: really-all

all-ao:    $(addsuffix .ao, $(ALDOR_FILES))
all-tests: $(addsuffix .ao, $(TEST_FILES))

define rec_dep_template
$(foreach l, $($1_deps), $(call rec_dep_template,$(l))) $(l)
endef

uniq_0 = $(if $1,$(firstword $1) $(call uniq,$(filter-out $(firstword $1),$1)))
uniq = $(call uniq_0,$1)
uniq_deps = $(call uniq,$(call rec_dep_template,$1))

$(addsuffix .ao, $(ALDOR_FILES)): %.ao: %.as
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
	$(ALDOR_$(X)) -laldor -lalgebra -fx=$@ $< $(addsuffix .ao, $(call uniq_deps,$*))

$(addsuffix .exe, $(TEST_FILES)): %.exe: %.ao lib$(LIB_NAME).a
	rm -f $@
	$(ALDOR_$(X)) -fx=$@ -l$(LIB_NAME) -lalgebra -laldor $*.ao

$(patsubst %,java/aldorcode/%.java,$(ALDOR_FILES)): java/aldorcode/%.java: %.ao
	mkdir -p java
	(cd java; $(ALDOR_$(X)) -fjava ../$*.ao)

.PHONY: java
java: $(patsubst %,java/%.java,$(ALDOR_FILES))

define dep_template
$1.ao: $(addsuffix .ao,$($1_deps))
endef

$(foreach l,$(ALDOR_FILES), $(eval $(call dep_template,$(l))))

clean:
	rm -f *.ao *.abn *.c *.fm *.al *.o *.exe
	rm -rf jars java

.PHONY: check $(addsuffix .exe-run, $(TEST_FILES))

check: $(addsuffix .exe-run, $(TEST_FILES))

$(addsuffix .exe-run, $(TEST_FILES)): %.exe-run: %.exe
	./$*.exe

.PHONY: classes
classes: java/classes.build

empty :=
space := $(empty) $(empty)
libnames := algebra aldor foam foamj

CLASSPATH:= $(subst $(space),:,$(patsubst %,$(ALDOR_SDK)/share/lib/%.jar,$(libnames)))

java/classes.build: $(patsubst %,java/aldorcode/%.java,$(ALDOR_FILES))
	echo $(CLASSPATH)
	(cd java; javac -cp $(CLASSPATH) $$(find . -name \*.java) )
	touch java/classes.build

jars/$(LIB_NAME).jar: java/classes.build
	mkdir -p jars
	(cd java; jar cf ../jars/$(LIB_NAME).jar .)

$(patsubst %,jars/%.jar,$(libnames)): jars/%: $(ALDOR_SDK)/share/lib/%
	mkdir -p jars
	cp $(ALDOR_SDK)/share/lib/$* $@

javadist: jars/$(LIB_NAME).jar $(patsubst %,jars/%.jar,$(libnames))

# Used to extract file information
idea:
	echo run: $(addsuffix .run, $(ALDOR_FILES))
	echo files: $(addsuffix .as, $(ALDOR_FILES))

really-all: javadist
