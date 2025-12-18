
#ifndef CRYPTOMINISAT5_EXPORT_H
#define CRYPTOMINISAT5_EXPORT_H

#ifdef CRYPTOMINISAT5_STATIC_DEFINE
#  define CRYPTOMINISAT5_EXPORT
#  define CRYPTOMINISAT5_NO_EXPORT
#else
#  ifndef CRYPTOMINISAT5_EXPORT
#    ifdef cryptominisat5_EXPORTS
        /* We are building this library */
#      define CRYPTOMINISAT5_EXPORT __attribute__((visibility("default")))
#    else
        /* We are using this library */
#      define CRYPTOMINISAT5_EXPORT __attribute__((visibility("default")))
#    endif
#  endif

#  ifndef CRYPTOMINISAT5_NO_EXPORT
#    define CRYPTOMINISAT5_NO_EXPORT __attribute__((visibility("hidden")))
#  endif
#endif

#ifndef CRYPTOMINISAT5_DEPRECATED
#  define CRYPTOMINISAT5_DEPRECATED __attribute__ ((__deprecated__))
#endif

#ifndef CRYPTOMINISAT5_DEPRECATED_EXPORT
#  define CRYPTOMINISAT5_DEPRECATED_EXPORT CRYPTOMINISAT5_EXPORT CRYPTOMINISAT5_DEPRECATED
#endif

#ifndef CRYPTOMINISAT5_DEPRECATED_NO_EXPORT
#  define CRYPTOMINISAT5_DEPRECATED_NO_EXPORT CRYPTOMINISAT5_NO_EXPORT CRYPTOMINISAT5_DEPRECATED
#endif

#if 0 /* DEFINE_NO_DEPRECATED */
#  ifndef CRYPTOMINISAT5_NO_DEPRECATED
#    define CRYPTOMINISAT5_NO_DEPRECATED
#  endif
#endif

#endif /* CRYPTOMINISAT5_EXPORT_H */
