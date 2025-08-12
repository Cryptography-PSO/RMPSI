cmake_minimum_required(VERSION 3.10)
project(volePSI)

configure_file(config.h.in "config.h" )

set(SRCS
    "RsOprf.cpp"
    "RsPsi.cpp"
    "SimpleIndex.cpp"
    "fileBased.cpp"
    "Mpsi.cpp"
    "fbMpsi.cpp"
)

if(VOLE_PSI_ENABLE_GMW)
    list(APPEND SRCS
        "GMW/Circuit.cpp"
        "GMW/Gmw.cpp"
        "GMW/SilentTripleGen.cpp"
    )
endif()

if(VOLE_PSI_ENABLE_CPSI)
    list(APPEND SRCS
        "RsCpsi.cpp"
    )
endif()

if(VOLE_PSI_ENABLE_OPPRF)
    list(APPEND SRCS
        "RsOpprf.cpp"
    )
endif()

add_library(volePSI STATIC ${SRCS})
target_link_libraries(volePSI oc::libOTe sparsehash libdivide)

# ------------- 查找 GMP -------------
find_library(GMP_LIB NAMES gmp libgmp.so libgmp.a PATHS /usr/lib /usr/local/lib)
find_path(GMP_INCLUDE_DIR gmp.h PATHS /usr/include /usr/local/include)
if(GMP_LIB AND GMP_INCLUDE_DIR)
    message(STATUS "Found GMP: ${GMP_LIB} (includes: ${GMP_INCLUDE_DIR})")
else()
    message(FATAL_ERROR "GMP not found. Please install GMP (sudo apt-get install libgmp-dev)")
endif()

# ------------- 查找 NTL -------------
find_library(NTL_LIB NAMES ntl PATHS /usr/local/lib /usr/lib)
find_path(NTL_INCLUDE_DIR NTL/ZZ.h PATHS /usr/local/include /usr/include)
if(NTL_LIB AND NTL_INCLUDE_DIR)
    message(STATUS "Found NTL: ${NTL_LIB} (includes: ${NTL_INCLUDE_DIR})")
else()
    message(FATAL_ERROR "NTL not found. Please install NTL with: sudo apt-get install libntl-dev")
endif()

# ================== 通用可执行文件宏 ==================
function(add_rmpis_target target_name source_file)
    add_executable(${target_name} ${source_file})

    # =================== BEGIN MODIFICATION ===================
    # 我们在这里使用链接器可识别的库名称（没有 ::）
    target_link_libraries(${target_name} 
        volePSI
        oc::libOTe
        coproto                  # 修正：使用真实库名
        macoro                   # 修正：使用真实库名
        cryptoTools              # 修正：使用真实库名
        sparsehash 
        libdivide
        ${NTL_LIB}
        ${GMP_LIB}
        Threads::Threads
        Boost::system
    )
    # ===================  END MODIFICATION  ===================

    target_include_directories(${target_name} PRIVATE
        ${NTL_INCLUDE_DIR}
        ${GMP_INCLUDE_DIR}
    )

    # Boost支持（如果启用）
    if(VOLE_PSI_ENABLE_BOOST)
        target_link_libraries(${target_name} Boost::thread)
        message(STATUS "Boost enabled for ${target_name}")
    endif()

    # Sodium支持（如果启用）
    if(VOLE_PSI_ENABLE_SODIUM)
        find_package(PkgConfig QUIET)
        if(PkgConfig_FOUND)
            pkg_check_modules(SODIUM libsodium)
            if(SODIUM_FOUND)
                target_link_libraries(${target_name} ${SODIUM_LIBRARIES})
                target_include_directories(${target_name} PRIVATE ${SODIUM_INCLUDE_DIRS})
                message(STATUS "Sodium enabled for ${target_name}")
            endif()
        endif()
    endif()

    # 编译选项设置
    if(APPLE)
        target_compile_options(${target_name} PRIVATE
            "-std=c++${VOLE_PSI_STD_VER}"
            "-Wno-pessimizing-move"
            "-Wno-delete-non-abstract-non-virtual-dtor"
            "-O3"
        )
    elseif(MSVC)
        set_target_properties(${target_name}
            PROPERTIES
                CXX_STANDARD ${VOLE_PSI_STD_VER}
                CXX_STANDARD_REQUIRED YES
                CXX_EXTENSIONS NO
        )
        if(VOLE_PSI_ENABLE_ASAN)
            target_compile_options(${target_name} PUBLIC "/fsanitize=address")
            target_link_options(${target_name} PUBLIC "/fsanitize=address")
        endif()
    else()
        # Linux/Unix编译选项
        target_compile_options(${target_name} PUBLIC
            "-std=c++${VOLE_PSI_STD_VER}"
            "-O3"
            "-DNDEBUG"
            "-march=native"
        )
        if(VOLE_PSI_ENABLE_ASAN)
            target_compile_options(${target_name} PUBLIC "-fsanitize=address")
            target_link_options(${target_name} PUBLIC "-fsanitize=address")
        endif()
    endif()

    # 平台特定设置
    if(MSVC)
        target_compile_definitions(${target_name} PUBLIC "_ENABLE_EXTENDED_ALIGNED_STORAGE")
    else()
        if(VOLE_PSI_ENABLE_SSE)
            target_compile_options(${target_name} PUBLIC -mavx)
        endif()
        if(VOLE_PSI_ENABLE_PIC)
            target_compile_options(${target_name} PUBLIC "-fPIC")
        endif()
    endif()

    # Release模式特定定义
    if(CMAKE_BUILD_TYPE STREQUAL "Release")
        target_compile_definitions(${target_name} PRIVATE 
            "NDEBUG"
            "VOLE_PSI_RELEASE"
        )
    endif()

    # 项目包含目录
    target_include_directories(${target_name} PUBLIC 
        $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/..>
        $<INSTALL_INTERFACE:include>
        $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/..>
    )

    # 构建信息输出
    message(STATUS "Building ${target_name} with the following configuration:")
    message(STATUS "  CMAKE_BUILD_TYPE: ${CMAKE_BUILD_TYPE}")
    message(STATUS "  NTL_LIB: ${NTL_LIB}")
    message(STATUS "  GMP_LIB: ${GMP_LIB}")

    # 安装规则（可选）
    if(CMAKE_INSTALL_PREFIX)
        install(TARGETS ${target_name}
            RUNTIME DESTINATION bin

        )
    endif()
endfunction()

# ================== 添加RMPSI_1和RMPSI_2可执行文件 ==================
if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/RMPSI_1.cpp")
    add_rmpis_target(RMPSI_1 RMPSI_1.cpp)
else()
    message(STATUS "RMPSI_1.cpp not found, skipping RMPSI_1 target")
endif()

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/RMPSI_2.cpp")
    add_rmpis_target(RMPSI_2 RMPSI_2.cpp)
else()
    message(STATUS "RMPSI_2.cpp not found, skipping RMPSI_2 target")
endif()

# ================== volePSI库自身的编译选项 ==================
if(APPLE)
    target_compile_options(volePSI PRIVATE
        "-std=c++${VOLE_PSI_STD_VER}"
        "-Wno-pessimizing-move"
        "-Wno-delete-non-abstract-non-virtual-dtor"
    )
elseif(MSVC)
    set_target_properties(volePSI
        PROPERTIES
            CXX_STANDARD ${VOLE_PSI_STD_VER}
            CXX_STANDARD_REQUIRED YES
            CXX_EXTENSIONS NO
    )
    if(VOLE_PSI_ENABLE_ASAN)
        message(WARNING "volepsi has ASAN enabled")
        target_compile_options(volePSI PUBLIC "/fsanitize=address")
        target_link_options(volePSI PUBLIC "/fsanitize=address")
    endif()
else()
    target_compile_options(volePSI PUBLIC
        "-std=c++${VOLE_PSI_STD_VER}"
    )
    if(VOLE_PSI_ENABLE_ASAN)
        message(WARNING "volepsi has ASAN enabled")
        target_compile_options(volePSI PUBLIC "-fsanitize=address")
        target_link_options(volePSI PUBLIC "-fsanitize=address")
    endif()
endif()

if(MSVC)
    target_compile_definitions(volePSI PUBLIC "_ENABLE_EXTENDED_ALIGNED_STORAGE")
else()
    if(VOLE_PSI_ENABLE_SSE)
        target_compile_options(volePSI PUBLIC -mavx)
    endif()
    if(VOLE_PSI_ENABLE_PIC)
        target_compile_options(volePSI PUBLIC "-fPIC")
    endif()
endif()

# volePSI包含目录
target_include_directories(volePSI PUBLIC 
    $<BUILD_INTERFACE:${CMAKE_CURRENT_BINARY_DIR}/..>
    $<INSTALL_INTERFACE:include>
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/..>
)
