#[cfg(target_os = "windows")]
mod windows {
    use crate::ffi;
    use std::collections::HashMap;
    use std::ffi::{c_void, CString};
    use std::sync::Mutex;

    type HANDLE = *mut c_void;
    type HMODULE = *mut c_void;
    type FARPROC = *mut c_void;
    type LPCSTR = *const i8;
    type DWORD = u32;
    type BOOL = i32;

    extern "system" {
        fn GetCurrentProcess() -> HANDLE;
        fn GetModuleHandleA(lpModuleName: LPCSTR) -> HMODULE;
        fn GetProcAddress(hModule: HMODULE, lpProcName: LPCSTR) -> FARPROC;
        fn K32EnumProcessModules(
            hProcess: HANDLE,
            lphModule: *mut HMODULE,
            cb: DWORD,
            lpcbNeeded: *mut DWORD,
        ) -> BOOL;
    }

    const LEAN_DLLS: &[&str] = &[
        "leanshared.dll",
        "libleanshared.dll",
        "leanshared_2.dll",
        "libleanshared_2.dll",
        "leanshared_1.dll",
        "libleanshared_1.dll",
        "Init_shared.dll",
        "libInit_shared.dll",
    ];

    static BSS_CACHE: Mutex<Option<HashMap<&'static str, usize>>> = Mutex::new(None);
    static FN_CACHE: Mutex<Option<HashMap<&'static str, usize>>> = Mutex::new(None);

    unsafe fn enum_process_modules() -> Vec<HMODULE> {
        let process = GetCurrentProcess();
        let mut needed = 0;
        let ok = K32EnumProcessModules(process, std::ptr::null_mut(), 0, &mut needed);
        if ok == 0 || needed == 0 {
            return Vec::new();
        }

        let module_count = needed as usize / std::mem::size_of::<HMODULE>();
        let mut modules = vec![std::ptr::null_mut(); module_count];
        let ok = K32EnumProcessModules(process, modules.as_mut_ptr(), needed, &mut needed);
        if ok == 0 {
            return Vec::new();
        }

        modules.truncate(needed as usize / std::mem::size_of::<HMODULE>());
        modules
    }

    unsafe fn resolve_bss_global(
        cache: &mut HashMap<&'static str, usize>,
        sym_name: &'static str,
        c_name: &CString,
        handle: HMODULE,
    ) -> Option<*mut ffi::lean_object> {
        let addr = GetProcAddress(handle, c_name.as_ptr());
        if addr.is_null() {
            return None;
        }

        let global_ptr = addr as *const *mut ffi::lean_object;
        let value = *global_ptr;
        cache.insert(sym_name, value as usize);
        Some(value)
    }

    unsafe fn resolve_function(
        cache: &mut HashMap<&'static str, usize>,
        sym_name: &'static str,
        c_name: &CString,
        handle: HMODULE,
    ) -> Option<*mut c_void> {
        let addr = GetProcAddress(handle, c_name.as_ptr());
        if addr.is_null() {
            return None;
        }

        cache.insert(sym_name, addr as usize);
        Some(addr)
    }

    unsafe fn lookup_with_cache<T>(
        cache: &Mutex<Option<HashMap<&'static str, usize>>>,
        sym_name: &'static str,
        resolver: unsafe fn(
            &mut HashMap<&'static str, usize>,
            &'static str,
            &CString,
            HMODULE,
        ) -> Option<*mut T>,
    ) -> *mut T {
        let mut guard = cache.lock().unwrap_or_else(|e| e.into_inner());
        let cache = guard.get_or_insert_with(HashMap::new);

        if let Some(&cached) = cache.get(sym_name) {
            return cached as *mut T;
        }

        let c_name = match CString::new(sym_name) {
            Ok(s) => s,
            Err(_) => {
                cache.insert(sym_name, 0);
                return std::ptr::null_mut();
            }
        };

        for dll_name in LEAN_DLLS {
            let c_dll = match CString::new(*dll_name) {
                Ok(s) => s,
                Err(_) => continue,
            };
            let handle = GetModuleHandleA(c_dll.as_ptr());
            if handle.is_null() {
                continue;
            }
            if let Some(value) = resolver(cache, sym_name, &c_name, handle) {
                return value;
            }
        }

        for handle in enum_process_modules() {
            if handle.is_null() {
                continue;
            }
            if let Some(value) = resolver(cache, sym_name, &c_name, handle) {
                return value;
            }
        }

        cache.insert(sym_name, 0);
        std::ptr::null_mut()
    }

    pub(super) unsafe fn lookup_bss_global(sym_name: &'static str) -> *mut ffi::lean_object {
        lookup_with_cache(&BSS_CACHE, sym_name, resolve_bss_global)
    }

    pub(super) unsafe fn lookup_function(sym_name: &'static str) -> *mut c_void {
        lookup_with_cache(&FN_CACHE, sym_name, resolve_function)
    }
}

#[cfg(target_os = "windows")]
#[inline]
pub unsafe fn required_bss_global(sym_name: &'static str) -> *mut crate::ffi::lean_object {
    let value = windows::lookup_bss_global(sym_name);
    assert!(
        !value.is_null(),
        "failed to resolve Lean exported global `{sym_name}` on Windows"
    );
    value
}

#[cfg(target_os = "windows")]
#[inline]
pub unsafe fn required_function(sym_name: &'static str) -> *mut std::ffi::c_void {
    let value = windows::lookup_function(sym_name);
    assert!(
        !value.is_null(),
        "failed to resolve Lean exported function `{sym_name}` on Windows"
    );
    value
}
