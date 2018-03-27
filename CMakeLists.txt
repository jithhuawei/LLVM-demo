add_library(FuncHookPass MODULE
	FuncHookPass.cpp
)

target_compile_features(FuncHookPass PRIVATE cxx_range_for cxx_auto_type)

set_target_properties(FuncHookPass PROPERTIES
    COMPILE_FLAGS "-fno-rtti"
)
