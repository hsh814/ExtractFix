add_library( LLVMFixLoc MODULE
  FixLocation.cpp
)

target_compile_features(LLVMFixLoc PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(LLVMFixLoc PROPERTIES
    COMPILE_FLAGS "-fno-rtti"
)

configure_file(fault_localization fault_localization COPYONLY)
