CXXFLAGS += $(shell llvm-config --cxxflags)
LDFLAGS += $(shell llvm-config --ldflags)

all : ghc-alias-analysis.so

%.o : %.cpp
	g++ -c ${CXXFLAGS} -o $@ $<

%.so : %.o
	g++ -shared ${LDFLAGS} -o $@ $<

