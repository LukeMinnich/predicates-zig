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
            const b_virtual = x - a;
            const a_virtual = x - b_virtual;
            const b_roundoff = b - b_virtual;
            const a_roundoff = a - a_virtual;
            const y = a_roundoff + b_roundoff;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
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
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ a_lo, a_hi };
        }

        fn twoProduct(a: T, b: T) Pair {
            const x = a * b;
            const a_lo, const a_hi = split(a);
            const b_lo, const b_hi = split(b);
            const err_1 = x - (a_hi * b_hi);
            const err_2 = err_1 - (a_lo * b_hi);
            const err_3 = err_2 - (a_hi * b_lo);
            const y = (a_lo * b_lo) - err_3;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ y, x };
        }

        fn square(a: T) Pair {
            const x = a * a;
            const a_lo, const a_hi = split(a);
            const err_1 = x - (a_hi * a_hi);
            const err_3 = err_1 - ((a_hi + a_hi) * a_lo);
            const y = (a_lo * a_lo) - err_3;
            // NOTE(luke): the result is ordered opposite of the the canonical order per predicates.c.
            return .{ y, x };
        }

        fn scaleExpansion(
            e: []const T,
            b: T,
            h: []T,
        ) []const T {
            return scaleExpansionCore(e, b, h, false);
        }

        fn scaleExpansionZeroElim(
            e: []const T,
            b: T,
            h: []T,
        ) []const T {
            return scaleExpansionCore(e, b, h, true);
        }

        fn scaleExpansionCore(
            e: []const T,
            b: T,
            h: []T,
            comptime perform_zero_elimination: bool,
        ) []const T {
            // std.debug.assert(e.len > 0);
            // std.debug.assert(h.len >= e.len * 2);
            // std.debug.assert(e.ptr != h.ptr);

            // PERF(luke): implementation in original `predicates.c` differs. Consider the potential
            // for performance optimization.

            var helper = HHelper(perform_zero_elimination).init(h);

            var h_val, var Q = twoProduct(e[0], b);
            helper.append(h_val);

            var i: usize = 1;
            while (i < e.len) : (i += 1) {
                const t_i, const T_i = twoProduct(e[i], b);
                h_val, const Q_tmp = twoSum(Q, t_i);
                helper.append(h_val);
                h_val, Q = fastTwoSum(T_i, Q_tmp);
                helper.append(h_val);
            }

            return helper.appendAndFinish(Q);
        }

        fn fastExpansionSum(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return fastExpansionSumCore(e, f, h, false);
        }

        fn fastExpansionSumZeroElim(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return fastExpansionSumCore(e, f, h, true);
        }

        fn fastExpansionSumCore(
            e: []const T,
            f: []const T,
            h: []T,
            comptime perform_zero_elimination: bool,
        ) []const T {
            std.debug.assert(e.len > 0);
            std.debug.assert(f.len > 0);
            std.debug.assert(h.len >= e.len + f.len);
            std.debug.assert(e.ptr != f.ptr);
            std.debug.assert(f.ptr != h.ptr);
            std.debug.assert(h.ptr != e.ptr);

            var helper = HHelper(perform_zero_elimination).init(h);
            var next = NextHelper.init(e, f);

            const g_0 = next.gByComparison();
            const g_1 = next.g();

            var h_val, var Q = fastTwoSum(g_1, g_0);
            helper.append(h_val);

            var i: usize = 2;
            while (i < e.len + f.len) : (i += 1) {
                h_val, Q = twoSum(Q, next.g());
                helper.append(h_val);
            }

            return helper.appendAndFinish(Q);
        }

        fn linearExpansionSum(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return linearExpansionSumCore(e, f, h, false);
        }

        fn linearExpansionSumZeroElim(
            e: []const T,
            f: []const T,
            h: []T,
        ) []const T {
            return linearExpansionSumCore(e, f, h, true);
        }

        /// Sums two expansions `e` and `f`, returning a subslice of `h` where the resulting
        /// expansion components reside. The resulting slice will always have at least one
        /// component. The components of the resulting slice will be in order of increasing
        /// magntidue, except any component may be zero when `perform_zero_elminiation` is false.
        fn linearExpansionSumCore(
            e: []const T,
            f: []const T,
            h: []T,
            comptime perform_zero_elimination: bool,
        ) []const T {
            std.debug.assert(e.len > 0);
            std.debug.assert(f.len > 0);
            std.debug.assert(h.len >= e.len + f.len);
            std.debug.assert(e.ptr != f.ptr);
            std.debug.assert(f.ptr != h.ptr);
            std.debug.assert(h.ptr != e.ptr);

            var helper = HHelper(perform_zero_elimination).init(h);
            var next = NextHelper.init(e, f);

            const g_0 = next.gByComparison();
            const g_1 = next.g();

            var q, var Q = fastTwoSum(g_1, g_0);

            var i: usize = 2;
            while (i < e.len + f.len) : (i += 1) {
                const h_val, const R_i = fastTwoSum(next.g(), q);
                helper.append(h_val);
                q, Q = twoSum(Q, R_i);
            }

            helper.append(q);
            return helper.appendAndFinish(Q);
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

        /// Helper for appending items to target `h` slice.
        fn HHelper(comptime perform_zero_elimination: bool) type {
            return struct {
                h: []T,
                h_idx: usize = 0,

                const Self = @This();

                fn init(h: []T) Self {
                    return .{ .h = h };
                }

                fn append(self: *Self, h_val: T) void {
                    if (!perform_zero_elimination or h_val != 0) {
                        self.h[self.h_idx] = h_val;
                        self.h_idx += 1;
                    }
                }

                // Returns a subslice of the backing slice `h`, where the result is guaranteed to
                // have a length of at least one.
                fn appendAndFinish(self: *Self, h_val: T) []const T {
                    // Append a zero component if and only if it's the largest (only) component.
                    if (!perform_zero_elimination or h_val != 0 or self.h_idx == 0) {
                        self.h[self.h_idx] = h_val;
                        self.h_idx += 1;
                    }
                    if (@import("builtin").mode == .Debug) {
                        // For ease of debugging, set a sentinel value for all elements in the
                        // target slice after the last resident element.
                        if (self.h.len - self.h_idx > 0) {
                            @memset(self.h[self.h_idx..], debugSentinel(T));
                        }
                    }
                    return self.h[0..self.h_idx];
                }
            };
        }

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

            const acxtail = twoDiffTail(a[0], c[0], acx);
            const bcxtail = twoDiffTail(b[0], c[0], bcx);
            const acytail = twoDiffTail(a[1], c[1], acy);
            const bcytail = twoDiffTail(b[1], c[1], bcy);

            // zig fmt: off
            if (    acxtail == 0 and acytail == 0
                and bcxtail == 0 and bcytail == 0) {
                return orient2DByDeterminant(det);
            }
            // zig fmt: on

            error_bound = (config.ccw_error_bound_c * det_sum + config.res_error_bound * @abs(det));
            det += (acx * bcytail + bcy * acxtail) - (acy * bcxtail + bcx * acytail);
            if (determinantExceedsErrorBound(det, error_bound)) {
                return orient2DByDeterminant(det);
            }

            // PERF(luke): determine if condensing the successive calls to
            // `linearExpansionSumZeroElim()` has any performance penalty.
            // I'm not convinced that saving a bit of stack size is worth sacrificing the clarity
            // of the underlying algorithm.

            // zig fmt: off
            const terms = [_][4]T{
                .{ acxtail, bcy    , acytail, bcx     },
                .{ acx    , bcytail, acy    , bcxtail },
                .{ acxtail, bcytail, acytail, bcxtail },
            };
            // zig fmt: on
            var expansion: []const T = &B;

            comptime var i: comptime_int = 0;
            inline while (i < 3) : (i += 1) {
                const s: Pair = twoProduct(terms[i][0], terms[i][1]);
                const t: Pair = twoProduct(terms[i][2], terms[i][3]);
                const u: [4]T = twoTwoDiff(s, t);
                var target: [4 + (i + 1) * 4]T = undefined;
                expansion = fastExpansionSumZeroElim(expansion, &u, &target);
            }

            return orient2DByDeterminant(expansion[expansion.len - 1]);
        }

        pub const CircleSense = enum {
            Inside,
            On,
            Outside,
        };

        fn inCircleByDeterminant(determinant: T) CircleSense {
            if (determinant > 0) {
                return .Inside;
            } else if (determinant < 0) {
                return .Outside;
            } else {
                return .On;
            }
        }

        pub fn inCircleInexact(a: Point2D, b: Point2D, c: Point2D, d: Point2D) CircleSense {
            const m11 = a[0] - d[0];
            const m12 = a[1] - d[1];
            const m13 = m11 * m11 + m12 * m12;

            const m21 = b[0] - d[0];
            const m22 = b[1] - d[1];
            const m23 = m21 * m21 + m22 * m22;

            const m31 = c[0] - d[0];
            const m32 = c[1] - d[1];
            const m33 = m31 * m31 + m32 * m32;

            // zig fmt: off
            const det = m11 * (m22 * m33 - m23 * m32)
                      - m12 * (m21 * m33 - m23 * m31)
                      + m13 * (m21 * m32 - m22 * m31);
            // zig fmt: on
            return inCircleByDeterminant(det);
        }

        pub fn inCircle(a: Point2D, b: Point2D, c: Point2D, d: Point2D) CircleSense {
            // PERF(luke): we may prefer to require the caller to orient the points in a
            // counter-clockwise order, to avoid the potentially expensive call to `orient2D`.
            // const a_, const b_, const c_ = points: {
            //     switch (orient2D(a, b, c)) {
            //         .Collinear => {
            //             // NOTE(luke): technically the results will be ambiguous between inside
            //             // circle and outside circle at this point
            //             break :points .{ a, b, c };
            //         },
            //         .CounterClockwise => {
            //             break :points .{ a, b, c };
            //         },
            //         .Clockwise => {
            //             break :points .{ a, c, b };
            //         },
            //     }
            // };

            const adx = a[0] - d[0];
            const bdx = b[0] - d[0];
            const cdx = c[0] - d[0];
            const ady = a[1] - d[1];
            const bdy = b[1] - d[1];
            const cdy = c[1] - d[1];

            // zig fmt: off
            const bdxcdy = bdx * cdy;
            const cdxbdy = cdx * bdy;
            const alift  = adx * adx
                         + ady * ady;

            const cdxady = cdx * ady;
            const adxcdy = adx * cdy;
            const blift  = bdx * bdx
                         + bdy * bdy;

            const adxbdy = adx * bdy;
            const bdxady = bdx * ady;
            const clift  = cdx * cdx
                         + cdy * cdy;

            const det = alift * (bdxcdy - cdxbdy)
                      + blift * (cdxady - adxcdy)
                      + clift * (adxbdy - bdxady);
            const permanent = (@abs(bdxcdy) + @abs(cdxbdy)) * alift
                            + (@abs(cdxady) + @abs(adxcdy)) * blift
                            + (@abs(adxbdy) + @abs(bdxady)) * clift;
            // zig fmt: on

            const error_bound = config.icc_error_bound_a * permanent;
            if (determinantExceedsErrorBound(det, error_bound)) {
                return inCircleByDeterminant(det);
            }
            return inCircleAdaptive(a, b, c, d, permanent);
        }

        pub fn inCircleAdaptive(a: Point2D, b: Point2D, c: Point2D, d: Point2D, permanent: T) CircleSense {
            const adx = a[0] - d[0];
            const bdx = b[0] - d[0];
            const cdx = c[0] - d[0];
            const ady = a[1] - d[1];
            const bdy = b[1] - d[1];
            const cdy = c[1] - d[1];

            const scale = scaleExpansionZeroElim;
            const sum = fastExpansionSumZeroElim;

            // The implementation ping-pongs between writing to each of these arrays. This is the
            // minimum size required from stages 1, 2, and 3, assuming no zero elimination occurs
            var fin_1_array: [1152]T = undefined;
            var fin_2_array: [1152]T = undefined;

            const Combo = struct {
                fn stage1(x_s: [2]T, y_s: [2]T, scale_factors: [2]T, u: *[4]T, output: *[32]T) []const T {
                    const s: Pair = twoProduct(x_s[0], y_s[0]);
                    const t: Pair = twoProduct(x_s[1], y_s[1]);
                    u.* = twoTwoDiff(s, t);

                    var tmp_output: [2][16]T = undefined;
                    var expansions: [2][]const T = undefined;

                    comptime var i: comptime_int = 0;
                    inline while (i < 2) : (i += 1) {
                        var tmp: [8]T = undefined;
                        const expansion = scale(u, scale_factors[i], &tmp);
                        expansions[i] = scale(expansion, scale_factors[i], &tmp_output[i]);
                    }

                    return sum(expansions[0], expansions[1], output);
                }

                fn stage2(
                    tail: T,
                    scale_these: [3][4]T,
                    scale_factors: [3]T,
                    begin_accum: []const T,
                    output: *[8]T,
                    curr: **[1152]T,
                    next: **[1152]T,
                ) struct {
                    []const T,
                    []const T,
                } {
                    var tmp16_: [3][16]T = undefined;
                    var tmp16: [3][]const T = undefined;

                    // NOTE(luke): this 8-component term is needed for later stage 3 computations
                    // though realistically, we could probably compute it again if needed
                    const stage_2 = stage_2: {
                        const res = scale(&scale_these[0], tail, output);
                        tmp16[0] = scale(res, scale_factors[0], &tmp16_[0]);

                        var i: usize = 1;
                        while (i < 3) : (i += 1) {
                            var tmp8_: [8]T = undefined;
                            const tmp8 = scale(&scale_these[i], tail, &tmp8_);
                            tmp16[i] = scale(tmp8, scale_factors[i], &tmp16_[i]);
                        }

                        break :stage_2 res;
                    };

                    const accum = accum: {
                        var tmp32_: [32]T = undefined;
                        var tmp48_: [48]T = undefined;

                        const tmp32 = sum(tmp16[0], tmp16[1], &tmp32_);
                        const tmp48 = sum(tmp32, tmp16[2], &tmp48_);

                        const result = sum(begin_accum, tmp48, curr.*);
                        break :accum result;
                    };

                    swap(curr, next);

                    return .{ stage_2, accum };
                }

                fn stage3(
                    main_pair: [2]T,
                    tail_pair: [2]T,
                    other_mains: [2][2]T,
                    other_tails: [2][2]T,
                    stage_2_parts: [2][]const T,
                    expansion: [2][4]T,
                    begin_accum: []const T,
                    curr: **[1152]T,
                    next: **[1152]T,
                ) []const T {
                    var accum = begin_accum;

                    if (tail_pair[0] != 0 or tail_pair[1] != 0) {
                        var perm_a_: [8]T = undefined;
                        var perm_b_: [4]T = undefined;

                        const perm_a, const perm_b = prefix: {
                            if (other_tails[0][0] != 0 or other_tails[0][1] != 0 or other_tails[1][0] != 0 or other_tails[1][1] != 0) {
                                var t_i = twoProduct(other_tails[0][0], other_mains[1][1]);
                                var t_j = twoProduct(other_mains[0][0], other_tails[1][1]);
                                const u = twoTwoSum(t_i, t_j);

                                t_i = twoProduct(other_tails[1][0], -other_mains[0][1]);
                                t_j = twoProduct(other_mains[1][0], -other_tails[0][1]);
                                const v = twoTwoSum(t_i, t_j);

                                const perm_a = sum(&u, &v, &perm_a_);

                                t_i = twoProduct(other_tails[0][1], other_tails[1][0]);
                                t_j = twoProduct(other_tails[1][0], other_tails[0][1]);
                                const perm_b = twoTwoDiff(t_i, t_j);
                                // PERF(luke): we could refactor to eliminate this memcpy
                                @memcpy(&perm_b_, perm_b[0..]);

                                break :prefix .{ perm_a, perm_b_[0..] };
                            } else {
                                perm_a_[0] = 0;
                                perm_b_[0] = 0;
                                break :prefix .{ perm_a_[0..1], perm_b_[0..1] };
                            }
                        };

                        if (tail_pair[0] != 0) {
                            const main: T = main_pair[0];
                            const tail: T = tail_pair[0];

                            var perm16_: [2][16]T = undefined;
                            var perm16: [2][]const T = undefined;

                            {
                                var tmp16_: [16]T = undefined;
                                var tmp32_: [32]T = undefined;
                                var tmp48_: [48]T = undefined;

                                const tmp16 = scale(stage_2_parts[0], tail, &tmp16_);
                                perm16[0] = scale(perm_a, tail, &perm16_[0]);
                                const tmp32 = scale(perm16[0], 2 * main, &tmp32_);
                                const tmp48 = sum(tmp16, tmp32, &tmp48_);

                                accum = sum(accum, tmp48, curr.*);
                                swap(curr, next);
                            }

                            inline for (other_tails, 0..) |other, idx| {
                                if (other[1] != 0) {
                                    var tmp8_: [8]T = undefined;
                                    var tmp16_: [16]T = undefined;
                                    const scale_me = if (idx == 0) tail else -tail;
                                    const tmp8 = scale(&expansion[idx], scale_me, &tmp8_);
                                    const tmp16 = scale(tmp8, other[1], &tmp16_);

                                    accum = sum(accum, tmp16, curr.*);
                                    swap(curr, next);
                                }
                            }

                            {
                                var tmp16_: [2][16]T = undefined;
                                var tmp32_: [2][32]T = undefined;
                                var tmp16: [2][]const T = undefined;
                                var tmp32: [2][]const T = undefined;
                                var tmp64_: [64]T = undefined;

                                tmp32[0] = scale(perm16[0], tail, &tmp32_[0]);
                                perm16[1] = scale(perm_b, tail, &perm16_[1]);
                                tmp16[0] = scale(perm16[1], 2 * main, &tmp16_[0]);
                                tmp16[1] = scale(perm16[1], tail, &tmp16_[1]);
                                tmp32[1] = sum(tmp16[0], tmp16[1], &tmp32_[1]);
                                const tmp64 = sum(tmp32[0], tmp32[1], &tmp64_);

                                accum = sum(accum, tmp64, curr.*);
                                swap(curr, next);
                            }
                        }
                        if (tail_pair[1] != 0) {
                            const main: T = main_pair[1];
                            const tail: T = tail_pair[1];

                            var perm16_: [2][16]T = undefined;
                            var perm16: [2][]const T = undefined;

                            {
                                var tmp16_: [16]T = undefined;
                                var tmp32_: [32]T = undefined;
                                var tmp48_: [48]T = undefined;

                                const tmp16 = scale(stage_2_parts[1], tail, &tmp16_);
                                perm16[0] = scale(perm_a, tail, &perm16_[0]);
                                const tmp32 = scale(perm16[0], 2 * main, &tmp32_);
                                const tmp48 = sum(tmp16, tmp32, &tmp48_);

                                accum = sum(accum, tmp48, curr.*);
                                swap(curr, next);
                            }
                            {
                                var tmp16_: [2][16]T = undefined;
                                var tmp32_: [2][32]T = undefined;
                                var tmp16: [2][]const T = undefined;
                                var tmp32: [2][]const T = undefined;
                                var tmp64_: [64]T = undefined;

                                tmp32[0] = scale(perm16[0], tail, &tmp32_[0]);
                                perm16[1] = scale(perm_b, tail, &perm16_[1]);
                                tmp16[0] = scale(perm16[1], 2 * main, &tmp16_[0]);
                                tmp16[1] = scale(perm16[1], tail, &tmp16_[1]);
                                tmp32[1] = sum(tmp16[0], tmp16[1], &tmp32_[1]);
                                const tmp64 = sum(tmp32[0], tmp32[1], &tmp64_);

                                accum = sum(accum, tmp64, curr.*);
                                swap(curr, next);
                            }
                        }
                    }

                    return accum;
                }

                fn swap(curr: **[1152]T, next: **[1152]T) void {
                    const swap_ = curr.*;
                    curr.* = next.*;
                    next.* = swap_;
                }
            };

            var bc_ca_ab: [3][4]T = undefined;
            var stage_1_arrays: [3][32]T = undefined;

            const stage_1_det = [_][]const T{
                Combo.stage1(.{ bdx, cdx }, .{ cdy, bdy }, .{ adx, ady }, &bc_ca_ab[0], &stage_1_arrays[0]),
                Combo.stage1(.{ cdx, adx }, .{ ady, cdy }, .{ bdx, bdy }, &bc_ca_ab[1], &stage_1_arrays[1]),
                Combo.stage1(.{ adx, bdx }, .{ bdy, ady }, .{ cdx, cdy }, &bc_ca_ab[2], &stage_1_arrays[2]),
            };

            const fin_1: []const T = fin_1: {
                var expansion: []const T = stage_1_det[0];
                var tmp: [64]T = undefined;
                expansion = sum(expansion, stage_1_det[1], &tmp);
                expansion = sum(expansion, stage_1_det[2], &fin_1_array);
                break :fin_1 expansion;
            };

            var det = estimate(fin_1);
            var error_bound = config.icc_error_bound_b * permanent;
            if (determinantExceedsErrorBound(det, error_bound)) {
                return inCircleByDeterminant(det);
            }

            const adxtail = twoDiffTail(a[0], d[0], adx);
            const adytail = twoDiffTail(a[1], d[1], ady);
            const bdxtail = twoDiffTail(b[0], d[0], bdx);
            const bdytail = twoDiffTail(b[1], d[1], bdy);
            const cdxtail = twoDiffTail(c[0], d[0], cdx);
            const cdytail = twoDiffTail(c[1], d[1], cdy);

            // zig fmt: off
            if (    adxtail == 0 and bdxtail == 0 and cdxtail == 0
                and adytail == 0 and bdytail == 0 and cdytail == 0) {
                return inCircleByDeterminant(det);
            }

            error_bound = config.icc_error_bound_c * permanent
                        + config.res_error_bound   * @abs(det);

            det += (  (adx * adx + ady * ady) * (  (bdx * cdytail + cdy * bdxtail)
                                                 - (bdy * cdxtail + cdx * bdytail))
                    + 2.0 * (adx * adxtail + ady * adytail) * (bdx * cdy - bdy * cdx))
                 + (  (bdx * bdx + bdy * bdy) * (  (cdx * adytail + ady * cdxtail)
                                                 - (cdy * adxtail + adx * cdytail))
                    + 2.0 * (bdx * bdxtail + bdy * bdytail) * (cdx * ady - cdy * adx))
                 + (  (cdx * cdx + cdy * cdy) * (  (adx * bdytail + bdy * adxtail)
                                                 - (ady * bdxtail + bdx * adytail))
                    + 2.0 * (cdx * cdxtail + cdy * cdytail) * (adx * bdy - ady * bdx));
            // zig fmt: on

            if (determinantExceedsErrorBound(det, error_bound)) {
                return inCircleByDeterminant(det);
            }

            var aa_bb_cc = [_][4]T{[_]T{0} ** 4} ** 3;

            {
                const tails: [3][2]T = .{
                    .{ bdxtail, bdytail },
                    .{ cdxtail, cdytail },
                    .{ adxtail, adytail },
                };

                const mains: [3][2]T = .{
                    .{ adx, ady },
                    .{ bdx, bdy },
                    .{ cdx, cdy },
                };

                var this: usize = 0;
                // zig fmt: off
                while (this < tails.len) : (this += 1) {
                    const next = (this + 1) % tails.len;
                    if (   tails[this][0] != 0.0 or tails[this][1] != 0.0
                        or tails[next][0] != 0.0 or tails[next][1] != 0.0) {
                        const t_0 = square(mains[this][0]);
                        const t_1 = square(mains[this][1]);
                        aa_bb_cc[this] = twoTwoSum(t_0, t_1);
                    }
                }
                // zig fmt: on
            }

            var curr = &fin_2_array;
            var next = &fin_1_array;
            var accum = fin_1;

            var stage_2_: [6][8]T = undefined;
            var stage_2: [6][]const T = undefined;

            const tails: [6]T = .{
                adxtail,
                adytail,
                bdxtail,
                bdytail,
                cdxtail,
                cdytail,
            };

            // stage 2
            {
                const expansions: [6][3][4]T = .{
                    .{ bc_ca_ab[0], aa_bb_cc[2], aa_bb_cc[1] },
                    .{ bc_ca_ab[0], aa_bb_cc[1], aa_bb_cc[2] },
                    .{ bc_ca_ab[1], aa_bb_cc[0], aa_bb_cc[2] },
                    .{ bc_ca_ab[1], aa_bb_cc[2], aa_bb_cc[0] },
                    .{ bc_ca_ab[2], aa_bb_cc[1], aa_bb_cc[0] },
                    .{ bc_ca_ab[2], aa_bb_cc[0], aa_bb_cc[1] },
                };

                const factors: [6][3]T = .{
                    .{ 2 * adx, bdy, -cdy },
                    .{ 2 * ady, cdx, -bdx },
                    .{ 2 * bdx, cdy, -ady },
                    .{ 2 * bdy, adx, -cdx },
                    .{ 2 * cdx, ady, -bdy },
                    .{ 2 * cdy, bdx, -adx },
                };

                for (tails, expansions, factors, 0..) |tail, scale_these, scale_factors, i| {
                    if (tail != 0) {
                        stage_2[i], accum = Combo.stage2(
                            tail,
                            scale_these,
                            scale_factors,
                            accum,
                            &stage_2_[i],
                            &curr,
                            &next,
                        );
                    } else {
                        stage_2_[i][0] = 1;
                        stage_2[i] = &stage_2_[i];
                    }
                }
            }

            // stage 3
            {
                const main_pairs: [3][2]T = .{
                    .{ adx, ady },
                    .{ bdx, bdy },
                    .{ cdx, cdy },
                };
                const tail_pairs: [3][2]T = .{
                    .{ adxtail, adytail },
                    .{ bdxtail, bdytail },
                    .{ cdxtail, cdytail },
                };
                const expansions: [3][2][4]T = .{
                    .{ aa_bb_cc[2], aa_bb_cc[1] },
                    .{ aa_bb_cc[0], aa_bb_cc[2] },
                    .{ aa_bb_cc[1], aa_bb_cc[0] },
                };

                for (
                    main_pairs,
                    tail_pairs,
                    expansions,
                    0..,
                ) |
                    main_pair,
                    tail_pair,
                    expansion,
                    i,
                | {
                    const other_mains: [2][2]T = .{
                        main_pairs[(i + 1) % main_pairs.len],
                        main_pairs[(i + 2) % main_pairs.len],
                    };
                    const other_tails: [2][2]T = .{
                        tail_pairs[(i + 1) % tail_pairs.len],
                        tail_pairs[(i + 2) % tail_pairs.len],
                    };
                    const stage_2_parts: [2][]const T = .{
                        stage_2[2 * i + 0],
                        stage_2[2 * i + 1],
                    };

                    accum = Combo.stage3(
                        main_pair,
                        tail_pair,
                        other_mains,
                        other_tails,
                        stage_2_parts,
                        expansion,
                        accum,
                        &curr,
                        &next,
                    );
                }
            }

            return inCircleByDeterminant(accum[accum.len - 1]);
        }

        fn estimate(expansion: []const T) T {
            var sum: T = 0;
            for (expansion) |component| {
                sum += component;
            }
            return sum;
        }

        fn twoTwoSum(a: [2]T, b: [2]T) [4]T {
            return mnSum(a.len, b.len, a, b);
        }

        fn twoTwoDiff(a: [2]T, b: [2]T) [4]T {
            return mnDiff(a.len, b.len, a, b);
        }

        fn mnSum(
            m: comptime_int,
            n: comptime_int,
            e: [m]T,
            f: [n]T,
        ) [m + n]T {
            var result: [m + n]T = undefined;
            mnExpansionOp(.{ .a = twoSum, .b = twoSum }, m, n, &e, &f, &result);
            return result;
        }

        fn mnDiff(
            m: comptime_int,
            n: comptime_int,
            e: [m]T,
            f: [n]T,
        ) [m + n]T {
            var result: [m + n]T = undefined;
            mnExpansionOp(.{ .a = twoDiff, .b = twoSum }, m, n, &e, &f, &result);
            return result;
        }

        const mnTailCb = struct {
            a: fn (T, T) Pair,
            b: fn (T, T) Pair,
        };

        fn growExpansion(
            m: comptime_int,
            b: T,
            h: []T,
            comptime cb: mnTailCb,
        ) void {
            std.debug.assert(h.len == m + 1);
            var Q = b;
            comptime var j: comptime_int = 0;
            inline while (j < m) : (j += 1) {
                // NOTE(luke): inputs to callback are in the reverse order of long version of the
                // original paper pseudocode.
                h[j], Q = if (j % 2 == 0) cb.a(h[j], Q) else cb.b(h[j], Q);
            }
            h[m] = Q;
        }

        fn mnExpansionOp(
            comptime cb: mnTailCb,
            m: comptime_int,
            n: comptime_int,
            e: []const T,
            f: []const T,
            h: []T,
        ) void {
            std.debug.assert(m > 0);
            std.debug.assert(n > 0);
            std.debug.assert(e.len == m);
            std.debug.assert(f.len == n);
            std.debug.assert(e.ptr != f.ptr);
            std.debug.assert(f.ptr != h.ptr);
            std.debug.assert(h.ptr != e.ptr);
            std.debug.assert(h.len == m + n);
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, e));
            std.debug.assert(subsequentComponentsAreNonDecreasingOrZero(T, f));

            @memcpy(h[0..m], e);
            comptime var i: comptime_int = 0;
            inline while (i < n) : (i += 1) {
                // PERF(luke): determine if inlining `growExpansion()` would impact performance
                growExpansion(m, f[i], h[i..(i + m + 1)], cb);
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

fn debugSentinel(T: type) T {
    const bytes = [_]u8{0xAA} ** @sizeOf(T);
    return std.mem.bytesToValue(T, &bytes);
}

test "linear expansion, w/ and w/o zero elimination" {
    const e = [_]f32{ 0.5, 1, 2, 4 };
    const f = [_]f32{ 0.5, 1, 2, 8 };

    {
        var g = [_]f32{debugSentinel(f32)} ** 8;
        const expansion = Context(f32).linearExpansionSum(&e, &f, &g);
        try std.testing.expectEqual(8, expansion.len);
        var sum: f32 = 0;
        var i: usize = 0;
        while (i < expansion.len) : (i += 1) {
            sum += g[i];
        }
        try std.testing.expectEqual(19, sum);
    }

    {
        var g = [_]f32{debugSentinel(f32)} ** 8;
        const expansion = Context(f32).linearExpansionSumZeroElim(&e, &f, &g);
        try std.testing.expectEqual(1, expansion.len);
        try std.testing.expectEqual(19, expansion[0]);
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

test "random point" {
    const Ctx = Context(f64);
    const p0 = Ctx.Point2D{ 0.5, 0.5 };
    const p1 = Ctx.Point2D{ 12, 12 };
    const p2 = Ctx.Point2D{ 24, 24 };

    var yd = p0[1];
    var xd: f64 = undefined;
    var row: usize = 0;
    while (row < 120) : (row += 1) {
        xd = p0[0];
        var col: usize = 0;
        while (col < 136) : (col += 1) {
            xd = std.math.nextAfter(f64, xd, std.math.inf(f64));
        }
        yd = std.math.nextAfter(f64, yd, std.math.inf(f64));
    }
    const p = Ctx.Point2D{ xd, yd };
    _ = Ctx.orient2D(p1, p, p2);
}

test "random point inCircle" {
    const Ctx = Context(f64);
    // zig fmt: off
    const p0 = Ctx.Point2D{ 0.5, 0.5 };
    const p1 = Ctx.Point2D{ 12, 12 };
    const p2 = Ctx.Point2D{ 24, 24 };
    const p3 = Ctx.Point2D{ -12, -12 };
    // zig fmt: on

    var p: Ctx.Point2D = p0;
    var i: usize = 0;
    while (i < 16) : (i += 1) {
        p = .{
            std.math.nextAfter(f64, p[0], std.math.inf(f64)),
            std.math.nextAfter(f64, p[1], std.math.inf(f64)),
        };
    }

    try std.testing.expectEqual(Ctx.CircleSense.On, Ctx.inCircle(p1, p2, p3, p));
}
