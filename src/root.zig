const std = @import("std");

pub fn Context(T: type) type {
    std.debug.assert(T == f32 or T == f64);

    return struct {
        const Pair = @Vector(2, T);
        // PERF(luke): determine if this is faster
        // const Pair = [2]T;

        // PERF(luke): consider adding `inline` to these primitive functions

        fn fastTwoSum(a: T, b: T) Pair {
            const x = a + b;
            const b_virtual = x - a;
            const y = b - b_virtual;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ y, x };
        }

        fn fastTwoDiff(a: T, b: T) Pair {
            const x = a - b;
            const b_virtual = a - x;
            const y = b_virtual - b;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ y, x };
        }

        fn twoSum(a: T, b: T) Pair {
            const x = a + b;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            const b_virtual = x - a;
            const a_virtual = x - b_virtual;
            const b_roundoff = b - b_virtual;
            const a_roundoff = a - a_virtual;
            const y = a_roundoff + b_roundoff;
            return .{ y, x };
        }

        fn twoDiff(a: T, b: T) Pair {
            const x = a - b;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ twoDiffTail(a, b, x), x };
        }

        fn twoDiffTail(a: T, b: T, x: T) T {
            const b_virtual = a - x;
            const a_virtual = x + b_virtual;
            const b_roundoff = b_virtual - b;
            const a_roundoff = a - a_virtual;
            return a_roundoff + b_roundoff;
        }

        fn split(a: T) Pair {
            const split_coeff = comptime floatSplitCoeff(T);
            const c = split_coeff * a;
            const a_big = c - a;
            const a_hi = c - a_big;
            const a_lo = a - a_hi;
            return .{ a_hi, a_lo };
        }

        fn twoProduct(a: T, b: T) Pair {
            const x = a * b;
            const a_hi, const a_lo = split(a);
            const b_hi, const b_lo = split(b);
            const err_1 = x - (a_hi * b_hi);
            const err_2 = err_1 - (a_lo * b_hi);
            const err_3 = err_2 - (a_hi * b_lo);
            const y = (a_lo * b_lo) - err_3;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ y, x };
        }

        fn linearExpansionSum(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return linearExpansionSumCore(false, e, f, h);
        }

        fn linearExpansionSumZeroElim(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return linearExpansionSumCore(true, e, f, h);
        }

        /// Sums two expansions `e` and `f`, returning a subslice of `h` where the resulting
        /// expansion components reside. The resulting slice will always have at least one
        /// component. The components of the resulting slice will be in order of increasing
        /// magntidue, except any component may be zero when `perform_zero_elminiation` is false.
        fn linearExpansionSumCore(
            comptime perform_zero_elimination: bool,
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            std.debug.assert(e.len > 0);
            std.debug.assert(f.len > 0);
            std.debug.assert(h.len >= e.len + f.len);

            var next = NextHelper.init(e, f);

            const g_0 = next.gByComparison();
            const g_1 = next.g();

            var q_i_minus_1, var Q_i_minus_1 = fastTwoSum(g_1, g_0);

            const m_plus_n = e.len + f.len;
            var result: usize = undefined;
            var i: usize = 2;
            if (perform_zero_elimination) {
                var h_idx: usize = 0;
                while (i < m_plus_n) : (i += 1) {
                    const maybe_h, const R_i = fastTwoSum(next.g(), q_i_minus_1);
                    q_i_minus_1, Q_i_minus_1 = twoSum(Q_i_minus_1, R_i);
                    if (maybe_h != 0) {
                        h[h_idx] = maybe_h;
                        h_idx += 1;
                    }
                }

                if (q_i_minus_1 != 0) {
                    h[h_idx] = q_i_minus_1;
                    h_idx += 1;
                }

                if (Q_i_minus_1 != 0 or h_idx == 0) {
                    // Ok to return a zero component if it's the largest component
                    h[h_idx] = Q_i_minus_1;
                    h_idx += 1;
                }

                result = h_idx;
            } else {
                while (i < m_plus_n) : (i += 1) {
                    h[i - 2], const R_i = fastTwoSum(next.g(), q_i_minus_1);
                    q_i_minus_1, Q_i_minus_1 = twoSum(Q_i_minus_1, R_i);
                }

                h[m_plus_n - 2] = q_i_minus_1;
                h[m_plus_n - 1] = Q_i_minus_1;

                result = m_plus_n;
            }

            if (@import("builtin").mode == .Debug) {
                // For ease of debugging, set a sentinel value for all elements in the target slice
                // after the last resident element.
                const len = h.len - result;
                if (len > 0) {
                    @memset(h[result..], debugSentinel(T));
                }
            }

            return h[0..result];
        }

        /// Helper for iterating over the components of two non-decreasing expansions and yielding
        /// the next component, as though the two expansions were merged into a single
        /// non-decreasing expansion.
        const NextHelper = struct {
            e: []const T,
            f: []const T,
            e_idx: usize = 0,
            f_idx: usize = 0,

            fn init(e: []const T, f: []const T) NextHelper {
                std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, e));
                std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, f));
                return NextHelper{
                    .e = e,
                    .f = f,
                };
            }

            fn gByBounds(self: *NextHelper) ?T {
                std.debug.assert(self.e_idx < self.e.len or self.f_idx < self.f.len);
                if (self.e_idx >= self.e.len) {
                    const value = self.f[self.f_idx];
                    self.f_idx += 1;
                    return value;
                } else if (self.f_idx >= self.f.len) {
                    const value = self.e[self.e_idx];
                    self.e_idx += 1;
                    return value;
                }
                return null;
            }

            fn gByComparison(self: *NextHelper) T {
                if (@abs(self.e[self.e_idx]) > @abs(self.f[self.f_idx])) {
                    const value = self.f[self.f_idx];
                    self.f_idx += 1;
                    return value;
                } else {
                    const value = self.e[self.e_idx];
                    self.e_idx += 1;
                    return value;
                }
            }

            fn g(self: *NextHelper) T {
                return self.gByBounds() orelse self.gByComparison();
            }
        };

        pub const Point2D = @Vector(2, T);

        pub const Orientation = enum {
            CounterClockwise,
            Collinear,
            Clockwise,
        };

        fn orient2DByDeterminant(determinant: T) Orientation {
            if (determinant > 0) {
                return .CounterClockwise;
            } else if (determinant < 0) {
                return .Clockwise;
            } else {
                return .Collinear;
            }
        }

        pub fn orient2DInexact(a: Point2D, b: Point2D, c: Point2D) Orientation {
            const det = (a[0] - c[0]) * (b[1] - c[1]) - (a[1] - c[1]) * (b[0] - c[0]);
            return orient2DByDeterminant(det);
        }

        pub fn orient2D(a: Point2D, b: Point2D, c: Point2D) Orientation {
            const det_l = (a[0] - c[0]) * (b[1] - c[1]);
            const det_r = (a[1] - c[1]) * (b[0] - c[0]);
            const det = det_l - det_r;

            const both_positive = det_l > 0 and det_r > 0;
            const both_negative = det_l < 0 and det_r < 0;

            // PERF(luke): consider the improvements claimed by the `robust` rust implementation
            if (both_positive or both_negative) {
                const det_sum = @abs(det_l + det_r);
                const error_bound = config.ccw_error_bound_a * det_sum;
                if (determinantExceedsErrorBound(det, error_bound)) {
                    return orient2DByDeterminant(det);
                }
                return orient2DAdaptive(a, b, c, det_sum);
            } else {
                return orient2DByDeterminant(det);
            }
        }

        fn determinantExceedsErrorBound(det: T, bound: T) bool {
            return det >= bound or -det >= bound;
            // PERF(luke): determine if this is faster
            // return @abs(det) >= error_bound;
        }

        fn orient2DAdaptive(a: Point2D, b: Point2D, c: Point2D, det_sum: T) Orientation {
            std.debug.assert(det_sum >= 0);

            const acx = a[0] - c[0];
            const bcx = b[0] - c[0];
            const acy = a[1] - c[1];
            const bcy = b[1] - c[1];

            const det_l = twoProduct(acx, bcy);
            const det_r = twoProduct(acy, bcx);

            const B: [4]T = twoTwoDiff(det_l, det_r);
            var det = estimate(&B);

            var error_bound = config.ccw_error_bound_b * det_sum;
            if (determinantExceedsErrorBound(det, error_bound)) {
                return orient2DByDeterminant(det);
            }

            const acx_tail = twoDiffTail(a[0], c[0], acx);
            const bcx_tail = twoDiffTail(b[0], c[0], bcx);
            const acy_tail = twoDiffTail(a[1], c[1], acy);
            const bcy_tail = twoDiffTail(b[1], c[1], bcy);

            if (acx_tail == 0 and acy_tail == 0 and bcx_tail == 0 and bcy_tail == 0) {
                return orient2DByDeterminant(det);
            }

            error_bound = (config.ccw_error_bound_c * det_sum + config.res_error_bound * @abs(det));
            det += (acx * bcy_tail + bcy * acx_tail) - (acy * bcx_tail + bcx * acy_tail);
            if (determinantExceedsErrorBound(det, error_bound)) {
                return orient2DByDeterminant(det);
            }

            // PERF(luke): determine if condensing the successive calls to
            // `linearExpansionSumZeroElim()` has any performance penalty.
            // I'm not convinced that saving a bit of stack size is worth sacrificing the clarity
            // of the underlying algorithm.

            const terms = [_][4]T{
                // zig fmt: off
                .{acx_tail, bcy     , acy_tail, bcx     },
                .{acx     , bcy_tail, acy     , bcx_tail},
                .{acx_tail, bcy_tail, acy_tail, bcx_tail},
                // zig fmt: on
            };
            var expansion: []const T = &B;

            comptime var i: comptime_int = 0;
            inline while (i < 3) : (i += 1) {
                const s: Pair = twoProduct(terms[i][0], terms[i][1]);
                const t: Pair = twoProduct(terms[i][2], terms[i][3]);
                const u: [4]T = twoTwoDiff(s, t);
                // PERF(luke): replace `linearExpansionSumZeroElim()` with
                // `fastExpansionSumZeroElim()`
                var target: [4 + (i + 1) * 4]T = undefined;
                expansion = linearExpansionSumZeroElim(expansion, &u, &target);
            }

            return orient2DByDeterminant(expansion[expansion.len - 1]);
        }

        fn estimate(expansion: []const T) T {
            var sum: T = 0;
            for (expansion) |component| {
                sum += component;
            }
            return sum;
        }

        fn mnSum(
            n_a: comptime_int,
            n_b: comptime_int,
            a_s: [n_a]T,
            b_s: [n_b]T,
        ) [n_a + n_b]T {
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, &a_s));
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, &b_s));
            return mnOpCore(n_a, n_b, &a_s, &b_s, .{ .a = twoSum, .b = twoSum });
        }

        fn mnDiff(
            n_a: comptime_int,
            n_b: comptime_int,
            a_s: [n_a]T,
            b_s: [n_b]T,
        ) [n_a + n_b]T {
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, &a_s));
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, &b_s));
            return mnOpCore(n_a, n_b, &a_s, &b_s, .{ .a = twoDiff, .b = twoSum });
        }

        fn twoTwoDiff(a: [2]T, b: [2]T) [4]T {
            return mnDiff(a.len, b.len, a, b);
        }

        const mnTailCb = struct {
            a: fn (T, T) Pair,
            b: fn (T, T) Pair,
        };

        fn mnOpCore(
            n_a: comptime_int,
            n_b: comptime_int,
            a_s: []const T,
            b_s: []const T,
            comptime cb: mnTailCb,
        ) [n_a + n_b]T {
            std.debug.assert(a_s.len == n_a);
            std.debug.assert(b_s.len == n_b);
            std.debug.assert(std.math.isPowerOfTwo(n_a));
            std.debug.assert(std.math.isPowerOfTwo(n_b));
            std.debug.assert(n_a >= n_b);
            std.debug.assert(n_a > 1);
            if (n_b > 1) {
                const half_n_b = n_b / 2;
                // See e.g. `Four_Two_Sum()` in the original `predicates.c`
                const t_0: [half_n_b + n_a]T = mnOpCore(n_a, half_n_b, a_s[0..], b_s[0..half_n_b], cb);
                const tmp_begin = half_n_b;
                const t_1: [half_n_b + n_a]T = mnOpCore(n_a, half_n_b, t_0[tmp_begin..], b_s[half_n_b..], cb);
                return t_0[0..tmp_begin].* ++ t_1;
            } else if (n_a > 2) {
                const half_n_a = n_a / 2;
                // See e.g. `Four_One_Sum()` in the original `predicates.c`
                const t_0: [1 + half_n_a]T = mnOpCore(half_n_a, 1, a_s[0..half_n_a], b_s[0..1], cb);
                const tmp_begin = (t_0.len - 1);
                const t_1: [1 + half_n_a]T = mnOpCore(half_n_a, 1, a_s[half_n_a..], t_0[tmp_begin..], cb);
                return t_0[0..tmp_begin].* ++ t_1;
            } else {
                // See e.g. `Two_One_Sum()` in the original `predicates.c`
                const l_0: T, const tmp: T = cb.a(a_s[0], b_s[0]);
                const l_1: T, const r_1: T = cb.b(a_s[1], tmp);
                return .{ l_0, l_1, r_1 };
            }
        }

        const config = config: {
            const epsilon = floatHalfEpsilon(T);
            break :config Config{
                // zig fmt: off
                .res_error_bound   =  ( 3 +    8 * epsilon) * epsilon,
                .ccw_error_bound_a =  ( 3 +   16 * epsilon) * epsilon,
                .ccw_error_bound_b =  ( 2 +   12 * epsilon) * epsilon,
                .ccw_error_bound_c =  ( 9 +   64 * epsilon) * epsilon * epsilon,
                .o3d_error_bound_a =  ( 7 +   56 * epsilon) * epsilon,
                .o3d_error_bound_b =  ( 3 +   28 * epsilon) * epsilon,
                .o3d_error_bound_c =  (26 +  288 * epsilon) * epsilon * epsilon,
                .icc_error_bound_a =  (10 +   96 * epsilon) * epsilon,
                .icc_error_bound_b =  ( 4 +   48 * epsilon) * epsilon,
                .icc_error_bound_c =  (44 +  576 * epsilon) * epsilon * epsilon,
                .isp_error_bound_a =  (16 +  224 * epsilon) * epsilon,
                .isp_error_bound_b =  ( 5 +   72 * epsilon) * epsilon,
                .isp_error_bound_c =  (71 + 1408 * epsilon) * epsilon * epsilon,
                // zig fmt: on
            };
        };

        const Config = struct {
            res_error_bound: T,
            ccw_error_bound_a: T,
            ccw_error_bound_b: T,
            ccw_error_bound_c: T,
            o3d_error_bound_a: T,
            o3d_error_bound_b: T,
            o3d_error_bound_c: T,
            icc_error_bound_a: T,
            icc_error_bound_b: T,
            icc_error_bound_c: T,
            isp_error_bound_a: T,
            isp_error_bound_b: T,
            isp_error_bound_c: T,
        };
    };
}

fn subsequentComponentsAreNonDecreasingOrZero(T: type, a: []const T) bool {
    std.debug.assert(a.len > 0);
    var i: usize = 0;
    var prev_nonzero: T = a[i];
    while (i < a.len - 1) : (i += 1) {
        if (a[i] != 0 and a[i + 1] != 0 and @abs(prev_nonzero) > @abs(a[i + 1])) {
            return false;
        }
        if (a[i + 1] != 0) {
            prev_nonzero = a[i + 1];
        }
    }
    return true;
}

test "test combinatorialSums" {
    const types = .{ f32, f64 };
    inline for (types) |@"type"| {
        const Ctx = Context(@"type");
        const @"1" = [_]@"type"{0} ** 1;
        const @"2" = [_]@"type"{0} ** 2;
        const @"4" = [_]@"type"{0} ** 4;
        const @"8" = [_]@"type"{0} ** 8;
        _ = Ctx.mnSum(@"8".len, @"4".len, @"8", @"4");
        _ = Ctx.mnSum(@"8".len, @"4".len, @"8", @"4");
        _ = Ctx.mnSum(@"8".len, @"2".len, @"8", @"2");
        _ = Ctx.mnSum(@"8".len, @"1".len, @"8", @"1");
        _ = Ctx.mnSum(@"4".len, @"4".len, @"4", @"4");
        _ = Ctx.mnSum(@"4".len, @"2".len, @"4", @"2");
        _ = Ctx.mnSum(@"4".len, @"1".len, @"4", @"1");
        _ = Ctx.mnSum(@"2".len, @"2".len, @"2", @"2");
        _ = Ctx.mnSum(@"2".len, @"1".len, @"2", @"1");
    }
}

pub fn sortAscendingMagnitude(comptime T: type) fn (void, T, T) bool {
    return struct {
        pub fn inner(_: void, a: T, b: T) bool {
            return @abs(a) < @abs(b);
        }
    }.inner;
}

test "test linearExpansionSum equivalent to combinatorialSums" {
    var prng = std.Random.DefaultPrng.init(0xDEADBEEF);
    const rand = prng.random();
    const Ctx = Context(f32);
    var components_4: [4]f32 = undefined;
    var components_2: [2]f32 = undefined;

    var i: usize = 0;
    while (i < 1000) : (i += 1) {
        for (&components_4) |*component| {
            component.* = rand.floatNorm(f32) * 1000;
        }
        for (&components_2) |*component| {
            component.* = rand.floatNorm(f32) * 1000;
        }
        std.mem.sort(
            f32,
            &components_4,
            {},
            sortAscendingMagnitude(f32),
        );
        std.mem.sort(
            f32,
            &components_2,
            {},
            sortAscendingMagnitude(f32),
        );

        const res_a: [6]f32 = Ctx.mnSum(components_4.len, components_2.len, components_4, components_2);

        var target: [6]f32 = undefined;
        const res_b = Ctx.linearExpansionSum(&components_4, &components_2, &target);

        var sum_a: f32 = 0;
        for (res_a) |component| {
            sum_a += component;
        }
        var sum_b: f32 = 0;
        for (res_b) |component| {
            sum_b += component;
        }

        try std.testing.expectEqual(sum_a, sum_b);
    }
}

fn debugSentinel(T: type) T {
    const bytes = [_]u8{0xAA} ** @sizeOf(T);
    return std.mem.bytesToValue(T, &bytes);
}

test "linear expansion, w/ and w/o zero elimination" {
    const e = [_]f32{ 0.5, 1, 2, 4 };
    const f = [_]f32{ 0.5, 1, 2, 4 };

    {
        var g = [_]f32{debugSentinel(f32)} ** 8;
        const expansion = Context(f32).linearExpansionSum(&e, &f, &g);
        try std.testing.expectEqual(8, expansion.len);
        var sum: f32 = 0;
        var i: usize = 0;
        while (i < expansion.len) : (i += 1) {
            sum += g[i];
        }
        try std.testing.expectEqual(15, sum);
    }

    {
        var g = [_]f32{debugSentinel(f32)} ** 8;
        const expansion = Context(f32).linearExpansionSumZeroElim(&e, &f, &g);
        try std.testing.expectEqual(1, expansion.len);
        try std.testing.expectEqual(15, expansion[0]);
    }
}

/// Returns the largest power of two whose value is such that 1.0 + value = 1.0 in floating-point
/// arithmetic. It bounds the relative roundoff error and is used for floating-point error analysis.
fn floatHalfEpsilon(T: type) T {
    return std.math.floatEps(T) / 2;
}

/// Returns the coefficient used to split floating-point numbers into two half-length significands
/// for exact multiplication.
fn floatSplitCoeff(T: type) T {
    // IEEE 754 encodes float values with the leading mantissa bit implied as 1, which is
    // not accounted for in `floatMantissaBits()`
    const p = std.math.floatMantissaBits(T) + 1;
    return @floatFromInt(computeSplitCoeff(p));
}

fn computeSplitCoeff(p: comptime_int) comptime_int {
    // Shewchuk's algorithms require p to have at least 4 significant bits
    std.debug.assert(p >= 4);
    const p_div_2_ceiling = (p + 1) >> 1;
    return (1 << (p_div_2_ceiling)) + 1;
}

test "test splitCoeff" {
    try std.testing.expectEqual(5, computeSplitCoeff(4));
    try std.testing.expectEqual(9, computeSplitCoeff(5));
    try std.testing.expectEqual(9, computeSplitCoeff(6));
    try std.testing.expectEqual(17, computeSplitCoeff(7));
    try std.testing.expectEqual(17, computeSplitCoeff(8));
}

/// This follows from `exactinit()` in the original `predicates.c`
fn shewchukEpsilonAndSplitter(T: type) struct { T, T } {
    var every_other: bool = true;
    var epsilon: T = 1.0;
    var splitter: T = 1.0;
    var check: T = 1.0;
    while (true) {
        const last_check = check;
        epsilon *= 0.5;
        if (every_other) {
            splitter *= 2.0;
        }
        every_other = !every_other;
        check = 1.0 + epsilon;
        if (check == 1.0 or check == last_check) {
            break;
        }
    }
    splitter += 1.0;
    return .{ epsilon, splitter };
}

test "test shewchukEpsilonAndSplitter" {
    const types = [_]type{ f32, f64 };
    inline for (types) |T| {
        const epsilon, const splitter = shewchukEpsilonAndSplitter(T);
        try std.testing.expectEqual(epsilon, floatHalfEpsilon(T));
        try std.testing.expectEqual(splitter, floatSplitCoeff(T));
    }
}

test "test orient2D" {
    const Ctx = Context(f32);
    const Point2D = Ctx.Point2D;
    // zig fmt: off
    const a    : Point2D = .{  0, 0 };
    const b    : Point2D = .{ 10, 0 };
    const p_col: Point2D = .{  5, 0 };
    const p_ccw: Point2D = .{  5, std.math.nextAfter(f32, 0,  1) };
    const p_cw : Point2D = .{  5, std.math.nextAfter(f32, 0, -1) };
    try std.testing.expectEqual(Ctx.orient2D(a, b, p_col), Ctx.Orientation.Collinear);
    try std.testing.expectEqual(Ctx.orient2D(a, b, p_ccw), Ctx.Orientation.CounterClockwise);
    try std.testing.expectEqual(Ctx.orient2D(a, b, p_cw ), Ctx.Orientation.Clockwise);
    // zig fmt: on
}
