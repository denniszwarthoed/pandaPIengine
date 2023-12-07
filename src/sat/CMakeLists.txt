file(GLOB sat_SRC "*.h" "*.cpp")

add_library(sat ${sat_SRC})
target_compile_options(sat PUBLIC ${compiler_flags})
target_link_options(sat PUBLIC ${linker_flags})

find_library(libcvc5.so.1 cvc5 HINTS ../../cvc5/build/src/)
target_link_libraries(sat PUBLIC ${libcvc5.so.1})
