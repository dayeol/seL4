/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 */

/*
 *
 * Copyright 2016, 2017 Hesham Almatary, Data61/CSIRO <hesham.almatary@data61.csiro.au>
 * Copyright 2015, 2016 Hesham Almatary <heshamelmatary@gmail.com>
 */

#include <assert.h>
#include <kernel/boot.h>
#include <machine/io.h>
#include <model/statedata.h>
#include <object/interrupt.h>
#include <arch/machine.h>
#include <arch/kernel/boot.h>
#include <arch/kernel/vspace.h>
#include <arch/benchmark.h>
#include <linker.h>
#include <plat/machine/hardware.h>
#include <plat/machine/fdt.h>
#include <machine.h>

/* Keystone Physical Addresses */
word_t keystone_paddr_base;
word_t keystone_paddr_load;

/* pointer to the end of boot code/data in kernel image */
/* need a fake array to get the pointer from the linker script */
extern char ki_boot_end[1];
/* pointer to end of kernel image */
extern char ki_end[1];

BOOT_CODE static bool_t
create_untypeds(cap_t root_cnode_cap, region_t boot_mem_reuse_reg)
{
    seL4_SlotPos   slot_pos_before;
    seL4_SlotPos   slot_pos_after;

    slot_pos_before = ndks_boot.slot_pos_cur;
    bool_t res = create_kernel_untypeds(root_cnode_cap, boot_mem_reuse_reg, slot_pos_before);

    slot_pos_after = ndks_boot.slot_pos_cur;
    ndks_boot.bi_frame->untyped = (seL4_SlotRegion) {
        slot_pos_before, slot_pos_after
    };
    return res;

}

BOOT_CODE cap_t
create_mapped_it_frame_cap(cap_t pd_cap, pptr_t pptr, vptr_t vptr, asid_t asid, bool_t
                           use_large, bool_t executable)
{
    cap_t cap;
    vm_page_size_t frame_size;

    if (use_large) {
        frame_size = RISCV_Mega_Page;
    } else {
        frame_size = RISCV_4K_Page;
    }

    cap = cap_frame_cap_new(
              asid,                            /* capFMappedASID       */
              pptr,                            /* capFBasePtr          */
              frame_size,                      /* capFSize             */
              wordFromVMRights(VMReadWrite),   /* capFVMRights         */
              0,                               /* capFIsDevice         */
              vptr                             /* capFMappedAddress    */
          );

    map_it_frame_cap(pd_cap, cap);
    return cap;
}

/**
 * Split mem_reg about reserved_reg. If memory exists in the lower
 * segment, insert it. If memory exists in the upper segment, return it.
 */
BOOT_CODE static region_t
insert_region_excluded(region_t mem_reg, region_t reserved_reg)
{
    region_t residual_reg = mem_reg;
    bool_t result UNUSED;

    if (reserved_reg.start < mem_reg.start) {
        /* Reserved region is below the provided mem_reg. */
        mem_reg.end = 0;
        mem_reg.start = 0;
        /* Fit the residual around the reserved region */
        if (reserved_reg.end > residual_reg.start) {
            residual_reg.start = reserved_reg.end;
        }
    } else if (mem_reg.end > reserved_reg.start) {
        /* Split mem_reg around reserved_reg */
        mem_reg.end = reserved_reg.start;
        residual_reg.start = reserved_reg.end;
    } else {
        /* reserved_reg is completely above mem_reg */
        residual_reg.start = 0;
        residual_reg.end = 0;
    }
    /* Add the lower region if it exists */
    if (mem_reg.start < mem_reg.end) {
        result = insert_region(mem_reg);
        assert(result);
    }
    /* Validate the upper region */
    if (residual_reg.start > residual_reg.end) {
        residual_reg.start = residual_reg.end;
    }

    return residual_reg;
}

BOOT_CODE static void
init_freemem(region_t ui_reg, region_t dtb_reg)
{
    unsigned int i;
    bool_t result UNUSED;
    region_t cur_reg;
    region_t res_reg[] = {
        {
            // We ignore all physical memory before the dtb as the current riscv-pk (proxy kernel)
            // that we use for loading is broken and provides an incorrect memory map where
            // it claims that the memory that is used to provide the m-mode services are
            // free physical memory. As there is no interface to determine what the memory
            // reserved for this is we simply hope it placed the dtb after itself and exclude
            // all memory up until then.
            .start = 0,
            .end = dtb_reg.end
        },
        {
            // This looks a bit awkward as our symbols are a reference in the kernel image window, but
            // we want to do all allocations in terms of the main kernel window, so we do some translation
            .start = (pptr_t)paddr_to_pptr(kpptr_to_paddr((void*)kernelBase)),
            .end   = (pptr_t)paddr_to_pptr(kpptr_to_paddr((void*)ki_end))
        },
        {
            .start = ui_reg.start,
            .end = ui_reg.end
        }
    };
    return;
    for (i = 0; i < MAX_NUM_FREEMEM_REG; i++) {
        ndks_boot.freemem[i] = REG_EMPTY;
    }

    /* Force ordering and exclusivity of reserved regions. */
    assert(res_reg[0].start < res_reg[0].end);
    assert(res_reg[1].start < res_reg[1].end);
    assert(res_reg[2].start < res_reg[2].end);

    assert(res_reg[0].end <= res_reg[1].start);
    assert(res_reg[1].end <= res_reg[2].start);

    for (i = 0; i < get_num_avail_p_regs(); i++) {
        cur_reg = paddr_to_pptr_reg(get_avail_p_reg(i));
        /* Adjust region if it exceeds the kernel window
         * Note that we compare physical address in case of overflow.
         */
        if (pptr_to_paddr((void*)cur_reg.end) > PADDR_TOP) {
            cur_reg.end = PPTR_TOP;
        }
        if (pptr_to_paddr((void*)cur_reg.start) > PADDR_TOP) {
            cur_reg.start = PPTR_TOP;
        }

        cur_reg = insert_region_excluded(cur_reg, res_reg[0]);
        cur_reg = insert_region_excluded(cur_reg, res_reg[1]);
        cur_reg = insert_region_excluded(cur_reg, res_reg[2]);

        if (cur_reg.start != cur_reg.end) {
            result = insert_region(cur_reg);
            assert(result);
        }
    }
}

BOOT_CODE static void
init_irqs(cap_t root_cnode_cap)
{
    irq_t i;

    for (i = 0; i <= maxIRQ; i++) {
        setIRQState(IRQInactive, i);
    }
    setIRQState(IRQTimer, KERNEL_TIMER_IRQ);

    /* provide the IRQ control cap */
    write_slot(SLOT_PTR(pptr_of_cap(root_cnode_cap), seL4_CapIRQControl), cap_irq_control_cap_new());
}

/* This and only this function initialises the CPU. It does NOT initialise any kernel state. */
extern char trap_entry[];

BOOT_CODE static void
init_cpu(void)
{

    /* Write trap entry address to stvec */
    write_stvec((word_t)trap_entry);

    activate_kernel_vspace();
}

/* This and only this function initialises the platform. It does NOT initialise any kernel state. */

BOOT_CODE static void
init_plat(paddr_t memstart, uint64_t memsize)
{
    keystoneFDT(memstart, memsize);
    //parseFDT((void*)dtb.start);
    initIRQController();
    initTimer();
}

/* Main kernel initialisation function. */

static BOOT_CODE bool_t
try_init_kernel(
    uint64_t dummy,
    paddr_t keystone_dram_base,
    uint64_t keystone_dram_size,
    paddr_t keystone_runtime_start,
    paddr_t keystone_user_start,
    paddr_t keystone_free_start,
    vptr_t  keystone_utm_ptr,
    uint64_t  keystone_utm_size
    //paddr_t ui_p_reg_start,
    //paddr_t ui_p_reg_end,
    //paddr_t dtb_p_reg_start,
    //paddr_t dtb_p_reg_end,
    //uint32_t pv_offset,
    //vptr_t  v_entry
)
{
    (void) dummy;
    cap_t root_cnode_cap;
    cap_t it_pd_cap;
    cap_t it_ap_cap;
    cap_t ipcbuf_cap;
    
    /* SeL4 Parameters */
    paddr_t ui_p_reg_start;
    paddr_t ui_p_reg_end;
    paddr_t free_start;
    paddr_t free_end;
    uint32_t pv_offset;
    vptr_t v_entry;
    /* Keystone Parameters */
    v_entry = read_sepc();
    ui_p_reg_start = keystone_user_start;
    ui_p_reg_end = keystone_user_start + keystone_free_start;
    free_start = keystone_free_start;
    free_end = keystone_dram_base + keystone_dram_size;
   
    pv_offset = keystone_user_start - 0x10000;
    
    keystone_paddr_base = keystone_dram_base;
    keystone_paddr_load = keystone_runtime_start;
    
    p_region_t boot_mem_reuse_p_reg = ((p_region_t) {
        kpptr_to_paddr((void*)KERNEL_BASE), kpptr_to_paddr(ki_boot_end)
    });
    region_t boot_mem_reuse_reg = paddr_to_pptr_reg(boot_mem_reuse_p_reg);
    region_t ui_reg = paddr_to_pptr_reg((p_region_t) {
        ui_p_reg_start, ui_p_reg_end
    });
    region_t dtb_reg = paddr_to_pptr_reg((p_region_t) {
        0, 0
    });
    pptr_t bi_frame_pptr;
    vptr_t bi_frame_vptr;
    vptr_t ipcbuf_vptr;
    create_frames_of_region_ret_t create_frames_ret;

    printf("ui_reg [0x%llx-0x%llx]\n",(unsigned long long) ui_reg.start, 
        (unsigned long long) ui_reg.end);
    printf("bootmem_reuse [0x%llx-0x%llx]\n",(unsigned long long) boot_mem_reuse_reg.start, 
        (unsigned long long) boot_mem_reuse_reg.end);
    /* convert from physical addresses to userland vptrs */
    v_region_t ui_v_reg;
    v_region_t it_v_reg;
    ui_v_reg.start = (uint32_t) (ui_p_reg_start - pv_offset);
    ui_v_reg.end   = (uint32_t) (ui_p_reg_end   - pv_offset);

    printf("ui_v_reg [0x%llx-0x%llx]\n", (unsigned long long) ui_v_reg.start, (unsigned long long) ui_v_reg.end);

    ipcbuf_vptr = ui_v_reg.end;
    bi_frame_vptr = ipcbuf_vptr + BIT(PAGE_BITS);

    /* The region of the initial thread is the user image + ipcbuf and boot info */
    it_v_reg.start = ui_v_reg.start;
    it_v_reg.end = bi_frame_vptr + BIT(PAGE_BITS);

    printf("it_v_reg [0x%llx-0x%llx]\n", (unsigned long long) it_v_reg.start, (unsigned long long) it_v_reg.end);
    printf("dram [0x%llx-0x%llx]\n", (unsigned long long) keystone_dram_base,
        (unsigned long long) keystone_dram_base + keystone_dram_size);
    printf("runt [0x%llx-0x%llx]\n", (unsigned long long) keystone_runtime_start,
        (unsigned long long) keystone_user_start);
    printf("user [0x%llx-0x%llx]\n", (unsigned long long) keystone_user_start,
        (unsigned long long) keystone_free_start);
    printf("free [0x%llx] (%d KB)\n", (unsigned long long) free_start,
        (int) (free_end - free_start)/1024);
    
    keystone_map_kernel_window(keystone_dram_base, keystone_dram_base + keystone_dram_size);
    map_kernel_window();

    /* initialise the CPU */
    init_cpu();

    /* initialize the platform */
    //init_plat(keystone_dram_base, keystone_dram_size);
    init_plat(keystone_dram_base, keystone_dram_size);

    /* make the free memory available to alloc_region() */
    init_freemem(ui_reg, dtb_reg); // this does nothing actually

    region_t cur_reg = ((region_t) {
        PPTR_BASE, PPTR_BASE + keystone_dram_size
        });
    region_t res_reg = paddr_to_pptr_reg((p_region_t) { 
        keystone_runtime_start, keystone_free_start
        });
    cur_reg = insert_region_excluded(cur_reg, res_reg);
    if(cur_reg.start < cur_reg.end)      
      assert(insert_region(cur_reg));

    /* create the root cnode */
    root_cnode_cap = create_root_cnode();
    if (cap_get_capType(root_cnode_cap) == cap_null_cap) {
        return false;
    }

    /* create the cap for managing thread domains */
    create_domain_cap(root_cnode_cap);

    /* create the IRQ CNode */
    if (!create_irq_cnode()) {
        return false;
    }

    /* initialise the IRQ states and provide the IRQ control cap */
    init_irqs(root_cnode_cap);

    /* create the bootinfo frame */
    bi_frame_pptr = allocate_bi_frame(0, CONFIG_MAX_NUM_NODES, ipcbuf_vptr);
    if (!bi_frame_pptr) {
        return false;
    }

    /* Construct an initial address space with enough virtual addresses
     * to cover the user image + ipc buffer and bootinfo frames */
    it_pd_cap = create_it_address_space(root_cnode_cap, it_v_reg);
    if (cap_get_capType(it_pd_cap) == cap_null_cap) {
        return false;
    }

    /* Create and map bootinfo frame cap */
    create_bi_frame_cap(
        root_cnode_cap,
        it_pd_cap,
        bi_frame_pptr,
        bi_frame_vptr
    );

    /* create the initial thread's IPC buffer */
    ipcbuf_cap = create_ipcbuf_frame(root_cnode_cap, it_pd_cap, ipcbuf_vptr);
    if (cap_get_capType(ipcbuf_cap) == cap_null_cap) {
        return false;
    }

    /* create all userland image frames */
    create_frames_ret =
        create_frames_of_region(
            root_cnode_cap,
            it_pd_cap,
            ui_reg,
            true,
            pv_offset
        );
    if (!create_frames_ret.success) {
        return false;
    }
    ndks_boot.bi_frame->userImageFrames = create_frames_ret.region;

    /* create the initial thread's ASID pool */
    it_ap_cap = create_it_asid_pool(root_cnode_cap);
    if (cap_get_capType(it_ap_cap) == cap_null_cap) {
        return false;
    }
    write_it_asid_pool(it_ap_cap, it_pd_cap);

    /* create the idle thread */
    if (!create_idle_thread()) {
        return false;
    }


    /* create the initial thread */
    tcb_t *initial = create_initial_thread(
                         root_cnode_cap,
                         it_pd_cap,
                         v_entry,
                         bi_frame_vptr,
                         ipcbuf_vptr,
                         ipcbuf_cap
                     );

    if (initial == NULL) {
        return false;
    }

    init_core_state(initial);

    /* convert the remaining free memory into UT objects and provide the caps */
    if (!create_untypeds(
                root_cnode_cap,
                boot_mem_reuse_reg)) {
        return false;
    }

    /* no shared-frame caps (RISCV has no multikernel support) */
    ndks_boot.bi_frame->sharedFrames = S_REG_EMPTY;

    /* finalise the bootinfo frame */
    bi_finalise();

    ksNumCPUs = 1;

    printf("Booting all finished, dropped to user space\n");
    return true;
}

BOOT_CODE VISIBLE void
init_kernel(
    uint64_t dummy,
    paddr_t keystone_dram_base,
    uint64_t keystone_dram_size,
    paddr_t keystone_runtime_start,
    paddr_t keystone_user_start,
    paddr_t keystone_free_start,
    vptr_t  keystone_utm_ptr,
    uint64_t  keystone_utm_size
    //paddr_t ui_p_reg_start,
    //paddr_t ui_p_reg_end,
    //sword_t pv_offset,
    //vptr_t  v_entry,
    //word_t hartid,
    //paddr_t dtb_output_p
)
{
    //pptr_t dtb_output = (pptr_t)paddr_to_pptr(dtb_output_p);

    //(void) dtb_output_p;

    bool_t result = try_init_kernel(dummy,
                                    keystone_dram_base,
                                    keystone_dram_size,
                                    keystone_runtime_start,
                                    keystone_user_start,
                                    keystone_free_start,
                                    keystone_utm_ptr,
                                    keystone_utm_size);

  /*
    bool_t result = try_init_kernel(ui_p_reg_start,
                                    ui_p_reg_end,
                                    0, //dtb_output_p,
                                    0, //dtb_output_p + fdt_size((void*)dtb_output),
                                    pv_offset,
                                    v_entry
                                   );
*/
    if (!result) {
        fail ("Kernel init failed for some reason :(");
    }

    schedule();
    activateThread();
}
