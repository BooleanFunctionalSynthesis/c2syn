# optional arguments:

#BUILD=RELEASE/DEBUG
# Architecture required by ABC; GMP required by Dsharp; No Unigen required by BFSS
CPP_FLAGS += -DLIN64 -DGMP_BIGNUM -DNO_UNIGEN
BUILD=DEBUG

C2Syn    = c2syn

ABC_PATH = ./dependencies/abc
DSHARP_PATH = ./dependencies/dsharp
BFSS_PATH = ./dependencies/bfss

ifndef CXX
CXX = g++
endif

BFSS_SRCDIR   = $(BFSS_PATH)/src
DSHARP_SRCDIR = $(DSHARP_PATH)/src
ABC_SRCDIR = $(ABC_PATH)/src
SRCDIR   = src
OBJDIR   = obj
BINDIR   = bin

TARGET_C2Syn  = $(BINDIR)/$(C2Syn)

ABC_INCLUDES = -I $(ABC_PATH) -I $(ABC_SRCDIR)
BFSS_INCLUDES = -I $(BFSS_SRCDIR)
DSHARP_INCLUDES = -I $(DSHARP_SRCDIR)/src_sharpSAT -I $(DSHARP_SRCDIR)/src_sharpSAT/MainSolver -I $(DSHARP_SRCDIR)/src_sharpSAT/MainSolver/InstanceGraph -I $(DSHARP_SRCDIR)/shared -I $(DSHARP_SRCDIR)/shared/Interface

LIB_DIRS = -L $(DSHARP_PATH) -L $(ABC_PATH) -L $(BFSS_PATH) -L /usr/lib/  

DIR_INCLUDES = -I. $(ABC_INCLUDES) $(BFSS_INCLUDES) $(DSHARP_INCLUDES) #$(LIB_DIRS) 

LIB_ABC    = -Wl,-Bstatic  -labc
LIB_DSHARP = -Wl,-Bstatic  -ldsharp
LIB_BFSS   = -Wl,-Bstatic -lcombfss
LIB_COMMON = -Wl,-Bdynamic -lm -ldl -lreadline -ltermcap -lpthread -fopenmp -lrt -Wl,-Bdynamic -lboost_program_options -Wl,-Bdynamic -lz

CPP_FLAGS += -std=c++11 
LFLAGS    = $(DIR_INCLUDES) -L $(ABC_PATH) $(LIB_ABC) -L$(DSHARP_PATH) $(LIB_DSHARP) -L/usr/lib -lgmpxx -lgmp -L $(BFSS_PATH) $(LIB_BFSS) $(LIB_COMMON)

ifeq ($(BUILD),DEBUG)
CPP_FLAGS += -O0 -g
else ifeq ($(BUILD),RELEASE)
CPP_FLAGS += -O3 -s -DNDEBUG
else
CPP_FLAGS += -O3
endif


BFSS_SOURCES  = $(BFSS_SRCDIR)/nnf.cpp $(BFSS_SRCDIR)/helper.cpp $(BFSS_SRCDIR)/readCnf.cpp
BFSS_OBJECTS  = $(BFSS_PATH)/obj
DSHARP_SOURCES = $(DSHARP_DIR)/src_sharpSAT/MainSolver $(DSHARP_DIR)/src/MainSolver.cpp_sharpSAT/MainSolver/InstanceGraph/InstanceGraph.cpp
DSHARP_OBJECTS = $(DSHARP_DIR)
C2Syn_SOURCES  = $(SRCDIR)/preprocess.cpp $(SRCDIR)/synNNF.cpp
C2Syn_OBJECTS  = $(C2Syn_SOURCES:$(SRCDIR)/%.cpp=$(OBJDIR)/%.o)

.PHONY: all clean remove c2syn directories
all: c2syn 
c2syn: directories $(TARGET_C2Syn)

directories:
	@mkdir -p $(OBJDIR)
	@mkdir -p $(BINDIR)

$(TARGET_C2Syn): $(C2Syn_OBJECTS) 
	$(CXX) $(CPP_FLAGS) -o $@ $^ $(LFLAGS)
	@echo "Built Target! - c2syn"


#$(C2Syn_OBJECTS): $(C2Syn_SOURCES)
#	$(CXX) $(CPP_FLAGS) -DNO_UNIGEN $^ -o $@ $(LFLAGS)
#	@echo "Compiled "$^" successfully!"
#	@echo "Built Target! - prep"


$(C2Syn_OBJECTS): $(OBJDIR)/%.o : $(SRCDIR)/%.cpp
	$(CXX) $(CPP_FLAGS) -c $^ -o $@  $(LFLAGS)
	@echo "Compiled "$<" successfully!"

clean:
	@$(RM) $(C2Syn_OBJECTS)
	@echo "Cleanup complete!"

remove: clean
	@$(RM) $(TARGET_C2Syn) 
	@echo "Executable removed!"
