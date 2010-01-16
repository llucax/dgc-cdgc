
# Build directory
B := build

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
	gc/iface.d \
	gc/alloc.d \
	gc/bits.d \
	gc/stats.d \
	gc/libc.d \
	gc/gc.d

# Default target
all: $B/cdgc.so

# Make the GC shared object
$B/cdgc.so: $(patsubst %.d,$B/%.o,$(sources))


# General pattern rules
#######################

$B/%.so: DCFLAGS += $(DC_SO_OPT)

$B/%.so:
	$(if $V,,@echo '  $(LD) $@')
	$(if $V,,@) $(LD) $(LDFLAGS) $(LD_SO_OPT) $(LD_OUTPUT_OPTION) $^

$B/%.o: %.d
	$(if $V,,@echo '  $(DC) $@')
	$(if $V,,@) $(DC) $(DCFLAGS) $(DC_OBJ_OPT) $(DC_OUTPUT_OPTION) $<

clean:
	$(if $V,,@echo '  $(RM) $B')
	$(if $V,,@) $(RM) -r $B

__dummy := $(shell mkdir -p $B)

