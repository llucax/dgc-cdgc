
# D compiler to use
DC := ldc

# DC compilation options to produce unlinked objects
DC_OBJ_OPT := -c

# DC compilation options to produce PIC objects
DC_SO_OPT := -relocation-model=pic

# DC option to tell where to store the output
DC_OUTPUT_OPTION = -of=$@

# Extra flags for the compiler
DCFLAGS := -O5 -release
#DCFLAGS := -debug

# Linker to use
LD := gcc

# Link options to produce a shared library
LD_SO_OPT = -fPIC -shared -Wl,-soname,$@

# DC option to tell where to store the output
LD_OUTPUT_OPTION = -o $@

# Extra flags for the linker
#LDFLAGS :=

# GC sources
sources := \
	gc.d \
	gcalloc.d \
	gcbits.d \
	gcstats.d \
	gcx.d

# Default target
all: cdgc.so

# Make the GC shared object
cdgc.so: $(sources:.d=.o)


# General pattern rules
#######################

%.so: DCFLAGS += $(DC_SO_OPT)

%.so:
	$(if $V,,@echo '  $(LD) $@')
	$(if $V,,@) $(LD) $(LDFLAGS) $(LD_SO_OPT) $(LD_OUTPUT_OPTION) $^

%.o: %.d
	$(if $V,,@echo '  $(DC) $@')
	$(if $V,,@) $(DC) $(DCFLAGS) $(DC_OBJ_OPT) $(DC_OUTPUT_OPTION) $<

