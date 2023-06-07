use hashbrown::HashSet;

const STD_FUNCTIONS_ARRAY: [&'static str; 28] = [
    "llvm.memcpy.p0i8.p0i8.i64",
    "malloc",
    "calloc",
    "strdup",
    "strndup",
    "llvm.memmove.p0i8.p0i8.i64",
    "realloc",
    "memchr",
    "free",
    "strlen",
    "strchr",
    "strtol",
    "strtoul",
    "strcmp",
    "strcasecmp",
    "strncmp",
    "fputc",
    "fputs",
    "fgets",
    "fwrite",
    "fcntl",
    "fsetxattr",
    "fclose",
    "fopen",
    "freopen",
    "fprintf",
    "clock_gettime",
    "gettimeofday",
];

lazy_static::lazy_static! {
    pub static ref STD_FUNCTIONS: HashSet<&'static str> = HashSet::from(STD_FUNCTIONS_ARRAY);
}
