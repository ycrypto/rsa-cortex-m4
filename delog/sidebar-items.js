initSidebarItems({"enum":[["Level","An enum representing the available verbosity levels of the logger."],["LevelFilter","An enum representing the available verbosity level filters of the logger."]],"fn":[["dequeue","The core \"read from circular buffer\" method. Marked unsafe to discourage use!"],["enqueue","The core \"write to circular buffer\" method. Marked unsafe to discourage use!"],["logger","Returns a reference to the logger (as `TryLogWithStatistics` implementation)"],["try_enqueue","The fallible \"write to circular buffer\" method. Marked unsafe to discourage use!"]],"macro":[["delog","Generate a deferred logger with specified capacity and flushing mechanism."],["generate_macros","Generate logging macros that can be gated by library."],["hex_str","Compactly format byte arrays and slices as hexadecimals."],["hexstr","More compactly format byte arrays and slices as hexadecimals."],["try_log","Fallible (ungated) version of `log!`."]],"mod":[["hex","Convenient `Display` and other traits for binary data."],["render","The default, minimal renderer, and some helper functions."]],"struct":[["Record","The \"payload\" of a log message."],["Statistics","Statistics on logger usage."]],"trait":[["Delogger","Semi-abstract characterization of the deferred loggers that the `delog!` macro produces."],["Flusher","A way to pass on logs, user supplied."],["Renderer","A way to format logs, user supplied."],["State","Trait for either state or statistics of loggers."],["TryLog","Fallible, panic-free version of the `log::Log` trait."],["TryLogWithStatistics","TryLog with some usage statistics on top."]]});