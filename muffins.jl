function vmid(muffins,students,alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    x = Int64((2*muffins - (W*students))/(V-W))
    y = Int64((2*muffins - (V*students))/(W-V))
    Wshares = W*y
    Vshares = V*x

    println("( ", Vshares, " " , V, "-shares )[0]( ", Wshares, " ", W, "-shares )")
    println("a", "      ", muffins,"/",students,"-",V-1,"a","    ",W-1,"a+(",muffins//students-(W-1),")     ","1-a" )
    println("There are no shares in the middle region. By buddying, there are no shares as well in [", 1-muffins//students+(W-1),"-",W-1,"a,",V-1,"a",1-muffins//students,"]")
    println("Adding this information as well as using the inputted alpha:")
    if Wshares>Vshares
        println("( ", Vshares, " " , V, "-shares )[    0    ]( ", Wshares-Vshares, " ", W, "-shares )[    0    ]( ",Vshares," ",W,"-shares)")
        println(alpha, "      ", muffins//students-(V-1)*alpha,"    ",(W-1)*alpha+muffins//students-(W-1),"        ",1-muffins//students+(W-1)-(W-1)*alpha,"       ",(V-1)*alpha+1-muffins//students,"    ",1-alpha )

    
        else 
        println("( ", Wshares, " " , V, "-shares )[    0    ]( ", Vshares-Wshares, " ", V, "-shares )[    0    ]( ",Wshares," ",W,"-shares)")
        println(alpha, "      ",1-muffins//students+(W-1)-(W-1)*alpha,"       ",(V-1)*alpha+1-muffins//students,"    ",muffins//students-(V-1)*alpha,"        ",(W-1)*alpha+muffins//students-(W-1),"     ",1-alpha )
    end

    println("1/2 is in the middle of the second interval. Thus, the number of shares in (", (V-1)*alpha+1-muffins//students,",1/2) and (1/2,",muffins//students-(V-1)*alpha,") is the same." )
    println("( ", Wshares, " " , V, "-shares )[    0    ]( ", "z", " ", V, "-shares | z", " ", V, "-shares )")
    println(alpha, "      ",1-muffins//students+(W-1)-(W-1)*alpha,"       ",(V-1)*alpha+1-muffins//students,"     1/2        ",muffins//students-(V-1)*alpha)
    println("Let us define the first interval as I_1, second interval as I_2, and third interval as I_3")
    println("Here z would be half of ", Vshares-Wshares, " which is ", Int32((Vshares-Wshares)/2),".")
    println("The following are the only possible types of students:")
    #do when V shares is greater too
    i1d=alpha
    i1u=1-muffins//students+(W-1)-(W-1)*alpha
    i2d=(V-1)*alpha+1-muffins//students
    i2u=1//2
    i3d=1//2
    i3u=muffins//students-(V-1)*alpha
    bounds=[alpha 1-muffins//students+(W-1)-(W-1)*alpha;(V-1)*alpha+1-muffins//students 1//2;1//2 muffins//students-(V-1)*alpha ]

n=V
    for i =0:n
        for j=i:n
            #println( i, j - i, n - j)
            if bounds[1]*i+bounds[2]*(j-i)+bounds[3]*(n-j)<muffins//students&& bounds[4]*i+bounds[5]*(j-i)+bounds[6]*(n-j)>muffins//students
                println("(1*",i,", 2*", j-i,", 3*",n-j,")")
            end
        end
    end
    println("Here, we get a contradiciton because the configurations above are impossible. Although the number of students with the above configuration should be a natural number, you get a rational number. Thus our proof is done.")


end
function Vmid(muffins, students, alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//students)*(1//(V-2))
    upperproof=(muffins//students)*(1//(V+1))
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q

    println("Claim: there is a (", muffins, ",", students,") procedure where the smallest share is ", alpha)
    println("")
    println("Each student will get either ", V, " or ", W, " shares")
    println("If there is a student with <=", V-2," shares, a share's buddy is >= than ", lowerproof, " which is < ", alpha)
    println("and if a student has >=", V+1, " shares, a share is >= than ", upperproof, " which is < ", alpha)
    println("While s_", V," is the number of ", V, "-shares and s_", W, " is the number of ", W, "-shares, we can set up the equations: ")
    println("The total number of shares: ", V, "s_",V," + ", W, "s_", W, " = ", 2*muffins)
    println("And the total number of students: s_",V," + s_", W, " = ", students)
    println("Once we solve, we get ", q, " students get ", V, " pieces and ", r, " students get ", W, " pieces, so there are ", Vshares, " ", V, "-shares and ", Wshares, " ", W, "-shares")
    println("")
    println("We can set up the interval graph: ")
    
    if Wshares > Vshares
        key = W
        x=(muffins//students)-((V-1)*alpha)
        y=(muffins//students)-((W-1)*(1-alpha))
        middleshares=Wshares-Vshares
        if x>y || y>1//2
            println("Bound error")
            return false
        end
        if (1-y)-1//2==1//2-y
            println("(",Vshares, " ", V, "-shares)(---0---)(", middleshares, " ", W, "-shares)(---0---)(", Vshares, " ", W, "-shares)")
            println(alpha, "        ", x, "  ", y, "   ", 1//2, "    ", 1-y, " ", 1-x, "        ", 1-alpha)
            println("")
            println("We now have three intervals. I1 is b/w ", 1-alpha, " and ", 1-x, " and contains ", Vshares, " shares")
            println("I2 is bw ", 1-y, " and ", 1//2, " and contains ", middleshares/2, " shares")
            println("I3 bw ", 1//2, " and ", y, " and contains ", middleshares/2, " shares")
            println("")
            println("Here are the possibilities for student shares: ")
        else
            println("Bound error")
        end

        n=W
        I1=Int64[]
        I2=Int64[]
        I3=Int64[]
        divide=false

            for i =0:n
                for j=i:n
                    check1=i*(1-alpha)+(j-i)*(1-y)+(n-j)*(1//2)
                    check2=i*(1-x)+(j-i)*(1//2)+(n-j)*(y)
                    if check1>muffins//students&&check2<muffins//students
                        if check2!=muffins//students
                            println("The student can have ", i, " I1 shares, ", j - i, " I2 shares, and ", n - j, " I3 shares")
                            push!(I1, i)
                            if i!=0
                            if(Vshares%i!=0) 
                                divide=true
                            end
                        end

                            push!(I2, j-i)
                            push!(I3, n-j)
                        else
                            continue
                        end
                    else
                        continue
                    end
                end
            end
        println("")
        println("y1 are the students with the first combo of shares, y2 are the students with the second combo of shares")
        println("Since I2=I3, we can set up these equations:")
        I3numb=maximum(I3)
        I2numb=maximum(I2)
        println("Eq 1: ", I3numb, "y1 = ", I2numb, " y2")
        println("Eq 2: y1 + y2 = ", r)
        println(I3numb+I2numb, "y = ", r)
        println("")


        if (r%(I3numb+I2numb))!=0 || divide
            println("There is a contradiction, since y isn't a natural number. The proof works.")
            return true
        else
            println("There is no contradiction. The proof does not work.")
            return false
        end

    elseif Vshares>Wshares
        y=1-((muffins//students)-((V-1)*alpha))
        x=1-((muffins//students)-((W-1)*(1-alpha)))
        if x>y || y>1//2
            println("Bound error")
            return false
        end
        middleshares=Vshares-Wshares
        if 1//2-(1-y)==y-1//2
            println("(",Wshares, " ", V, "-shares)(---0---)(", middleshares, " ", V, "-shares)(---0---)(", Wshares, " ", W, "-shares)")
            println(alpha, "      ", x, " ", y, "   ", 1//2, "  ", 1-y, "  ", 1-x, "      ", 1-alpha)
            println("")
            println("We now have three intervals. I1 is b/w ", alpha, " and ", x, " and contains ", Vshares, " shares")
            println("I2 is bw ", y, " and ", 1//2, " and contains ", middleshares/2, " shares")
            println("I3 bw ", 1//2, " and ", y, " and contains ", middleshares/2, " shares")
            println("")
            println("Here are the possibilities for student shares: ")

            n=V
            I1=Int64[]
            I2=Int64[]
            I3=Int64[]
            divide=false

                for i =0:n
                    for j=i:n
                        check1=i*x+(j-i)*1//2+(n-j)*(1-y)
                        check2=i*alpha+(j-i)*y+(n-j)*(1//2)
                        if check1>muffins//students&&check2<muffins//students
                            if check2!=muffins//students
                                println("The student can have ", i, " I1 shares, ", j - i, " I2 shares, and ", n - j, " I3 shares")
                                push!(I1, i)
                                if i!=0
                                if(Wshares%i!=0) 
                                    divide=true
                                end
                            end
                                push!(I2, j-i)
                                push!(I3, n-j)
                            else
                                continue
                            end
                        else
                            continue
                        end
                    end
                end
        println("")
        println("y1 are the students with the first combo of shares, y2 are the students with the second combo of shares")
        println("Since I2=I3, we can set up these equations:")
        I3numb=maximum(I3)
        I2numb=maximum(I2)
        println("Eq 1: ", I3numb, "y1 = ", I2numb, " y2")
        println("Eq 2: y1 + y2 = ", q)
        println(I3numb+I2numb, "y = ", q)
        println("")
        if (q%(I3numb+I2numb))!=0 || divide
            println("There is a contradiction, since y isn't a natural number. The proof works.")
            return true
        else
            println("There is no contradiction. The proof does not work.")
            return false
        end
            end
        end
end

function VmidA(muffins, students, alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//students)*(1//(V-2))
    upperproof=(muffins//students)*(1//(V+1))
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q

    
    if Wshares > Vshares
        key = W
        x=(muffins//students)-((V-1)*alpha)
        y=(muffins//students)-((W-1)*(1-alpha))
        middleshares=Wshares-Vshares
        if x>y || y>1//2

            return false
        end
        if (1-y)-1//2==1//2-y

        else

        end

        n=W

        divide=false
        I3numb=-5
        I2numb=-5
            for i =0:n
                for j=i:n
                    check1=i*(1-alpha)+(j-i)*(1-y)+(n-j)*(1//2)
                    check2=i*(1-x)+(j-i)*(1//2)+(n-j)*(y)
                    if check1>muffins//students&&check2<muffins//students
                        if check2!=muffins//students

                            if i!=0
                            if(Vshares%i!=0) 
                                divide=true
                            end
                        end

                            I3numb=max(I3numb, j-i)
                            I2numb=max(I2numb, n-j)
                        else
                            continue
                        end
                    else
                        continue
                    end
                end
            end



        if (r%(I3numb+I2numb))!=0 || divide

            return true
        else

            return false
        end

    elseif Vshares>Wshares
        y=1-((muffins//students)-((V-1)*alpha))
        x=1-((muffins//students)-((W-1)*(1-alpha)))
        if x>y || y>1//2

            return false
        end
        middleshares=Vshares-Wshares
        if 1//2-(1-y)==y-1//2
          

            n=V

            divide=false
            I3numb=-5
            I2numb=-5

                for i =0:n
                    for j=i:n
                        check1=i*x+(j-i)*1//2+(n-j)*(1-y)
                        check2=i*alpha+(j-i)*y+(n-j)*(1//2)
                        if check1>muffins//students&&check2<muffins//students
                            if check2!=muffins//students

                                if i!=0
                                if(Wshares%i!=0) 
                                    divide=true
                                end
                            end
                                I2numb=max(I2numb, j-i)
                                I3numb=max(I3numb, n-j)
                            else
                                continue
                            end
                        else
                            continue
                        end
                    end
                end

        if ((q%(I3numb+I2numb))!=0 || divide)
            return true
        else

            return false
        end
            end
        end
end
function VmidB(muffins, students, alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//students)*(1//(V-2))
    upperproof=(muffins//students)*(1//(V+1))
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q

    if Wshares > Vshares
        key = W
        x=(muffins//students)-((V-1)*alpha)
        y=(muffins//students)-((W-1)*(1-alpha))
        middleshares=Wshares-Vshares
        if alpha>=x||x>=y
            return false
        elseif (1-y)-1//2==1//2-y
            return true

        n=W
        I1=Int64[]
        I2=Int64[]
        I3=Int64[]

            for i =0:n
                for j=i:n
                    check1=i*(1-alpha)+(j-i)*(1-y)+(n-j)*(1//2)
                    check2=i*(1-x)+(j-i)*(1//2)+(n-j)*(y)
                    if check1>muffins//students&&check2<muffins//students
                        if check2!=muffins//students
                            push!(I1, i)
                            push!(I2, j-i)
                            push!(I3, n-j)
                        else
                            continue
                        end
                    else
                        continue
                    end
                end
            end
        end
        I3numb=maximum(I3)
        I2numb=maximum(I2)
        I1numb=maximum(I1)
        I1numb2=minimum(I1)

        if (r%(I3numb+I2numb))!=0||(q%(I1numb+I1numb2))!=0
            return true
        else
            return false
        end

    elseif Vshares>Wshares
        y=1-((muffins//students)-((V-1)*alpha))
        x=1-((muffins//students)-((W-1)*(1-alpha)))

        middleshares=Vshares-Wshares
        if alpha>=x||x>=y
            return false
        elseif 1//2-(1-y)==y-1//2

            n=V
            I1=Int64[]
            I2=Int64[]
            I3=Int64[]


                for i =0:n
                    for j=i:n
                        check1=i*x+(j-i)*1//2+(n-j)*(1-y)
                        check2=i*alpha+(j-i)*y+(n-j)*(1//2)
                        if check1>muffins//students&&check2<muffins//students
                            if check2!=muffins//students
                                push!(I1, i)
                                push!(I2, j-i)
                                push!(I3, n-j)
                            else
                                continue
                            end
                        else
                            continue
                        end
                    end
                end

        I3numb=maximum(I3)
        I2numb=maximum(I2)
        I1numb=maximum(I1)
        I1numb2=minimum(I1)

        if (q%(I3numb+I2numb))!=0||(r%(I1numb+I1numb2))!=0
            return true
        else
            return false
        end
            end
        end
end
function mid(muffins,students)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//students)*(1//(V-2))
    upperproof=(muffins//students)*(1//(V+1))
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q
    answer=0 
    if Vshares>Wshares
        n=V
    for i =0:n
        for j=i:n
            println( i, j - i, n - j)            
            alpha1=(i*(1-muffins//students+(W-1))+(j-i)*1//2+(n-j-1)*muffins//students)//(i*(W-1)+(n-j)*(V-1))
            alpha2=(muffins//students-(j-i)*(1-muffins//students)-(n-j)*1//2)//(i+(j-i)*(V-1))
            print(alpha1, " ", VmidB(muffins,students,alpha1)," ")
            println(alpha2, " ", VmidB(muffins,students,alpha2)," ")
            if(VmidB(muffins,students,alpha1)&&alpha1>1//3)
                answer=max(alpha1,answer)
            end
            if(VmidB(muffins,students,alpha2) &&alpha2>1//3)
                answer=max(alpha2,answer)
            end

        end
    end
end
if Wshares>Vshares
    n=W
    for i =0:n
        for j=i:n
            println( i, j - i, n - j)
            newdown1=1-(muffins//students)+(W-1)
            
            #alpha2=(muffins//students-(j-i)*(1-muffins//students)-(n-j)*1//2)//(i+(j-i)*(V-1))
         alpha1=(i*(1//2)+(j-i)*(1-muffins//students+(W-1))+(n-j)-muffins//students)//(n-j+(j-i)*(W-1))
                alpha2=(muffins//students-i*(muffins//students-(W-1))+(j-i)*(1//2)-(n-j)*(1-muffins//students))//(i*(W-1)+(n-j)*(V-1))
            print(alpha1, " ", VmidB(muffins,students,alpha1)," ")
            println(alpha2, " ", VmidB(muffins,students,alpha2)," ")
            if(VmidB(muffins,students,alpha1)&&alpha1>1//3)
                answer=max(alpha1,answer)
            end
            if(VmidB(muffins,students,alpha2)&&alpha2>1//3)
                answer=max(alpha2,answer)
            end
        end
    end
end
println(answer)
    
end

function vint(muffins,students)
    
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    x = Int64((2*muffins - (W*students))/(V-W))
    y = Int64((2*muffins - (V*students))/(W-V))
    Wshares = W*y
    Vshares = V*x
    println("Let 'a' be the upper bound larger than 1/3.")
    println("We have ", 2*muffins, " pieces,", Vshares," ", V,"-shares and ", Wshares," ",W,"-shares.")
    println("If the smallest ", W,"-share is size y then ", W-1,"(1-a)+y>",muffins,"/",students,", so y>",W-1,"a",muffins//students-(W-1))
    println("Thus, ", W-1,"a+(",muffins//students-(W-1), ") is the left endpoint of the ", W,"-share interval.")
    println("Likewise, if the largest ", V,"-share is of size x, then ", V-1,"a+x<",muffins,"/",11, " so x<",muffins,"/",students,"-",V-1,"a, which would be the right endpoint of the ", V,"-share interval.")
    println("The following diagram visualizes this information.")
    println("( ", Vshares, " " , V, "-shares )[0]( ", Wshares, " ", W, "-shares )")
    println("a", "      ", muffins,"/",students,"-",V-1,"a","    ",W-1,"a+(",muffins//students-(W-1),")     ","1-a" )
    println("There are no shares in the middle region. By buddying, there are no shares as well in [", 1-muffins//students+(W-1),"-",W-1,"a,",V-1,"a",1-muffins//students,"]")
    
    println("The following picture adds the new detail mentioned.")
    if Wshares>Vshares
    println("( ", Vshares, " " , V, "-shares )[    0    ]( ", Wshares-Vshares, " ", W, "-shares )[    0    ]( ",Vshares," ",W,"-shares)")
    println("a", "      ", muffins,"/",students,"-",V-1,"a","    ",W-1,"a+(",muffins//students-(W-1),")        ",1-muffins//students+(W-1),"-",W-1,"a      ",V-1,"a",1-muffins//students,"    1-a" )
    newdown=1-muffins//students+(W-1)
    key=Int64(floor(Vshares/y))
    other=W-key
    answer= (key+other*newdown-muffins//students)//(key+other*(W-1))
    print("Left: We find a such that someone has to have >=", key+1," shares. If he or she had <=", key, " shares then she has ")
    println("a >= ",answer)


    else 
    println("( ", Wshares, " " , V, "-shares )[    0    ]( ", Vshares-Wshares, " ", V, "-shares )[    0    ]( ",Wshares," ",W,"-shares)")
    println("a", "      ",1-muffins//students+(W-1),"-",W-1,"a      ",V-1,"a",1-muffins//students,"    ",muffins,"/",students,"-",V-1,"a","        ",W-1,"a+(",muffins//students-(W-1),")    1-a" )
    key=Int64(floor((Vshares-Wshares)/x))
    other=V-key
    answer=(other*(1-muffins//students+(W-1))+(key-1)*(muffins//students))//(other+key*(V-1))
    print("We find a such that someone has to have >=", key+1," shares. If he or she had <=", key, " shares then she has ")
    println("a >= ",answer)

    end

    if(answer<1/3)
        println("Since our solution is less than 1/3, our assumption must be wrong. This leaves our answer to be 1/3")
    
    end

end

function Vint(muffins, students, alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//students)*(1//(V-2))
    upperproof=(muffins//students)*(1//(V+1))
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q


    println("Claim: there is a (", muffins, ",", students,") procedure where the smallest share is ", alpha)
    println("")
    println("Each student will get either ", V, " or ", W, " shares")
    println("If there is a student with <=", V-2," shares, a share's buddy is >= than ", lowerproof, " which is < ", alpha)
    println("and if a student has >=", V+1, " shares, a share is >= than ", upperproof, " which is < ", alpha)
    println("While s_", V," is the number of ", V, "-shares and s_", W, " is the number of ", W, "-shares, we can set up the equations: ")
    println("The total number of shares: ", V, "s_",V," + ", W, "s_", W, " = ", 2*muffins)
    println("And the total number of students: s_",V," + s_", W, " = ", students)
    println("Once we solve, we get ", q, " students get ", V, " pieces and ", r, " students get ", W, " pieces, so there are ", Vshares, " ", V, "-shares and ", Wshares, " ", W, "-shares")
    println("")
    println("We can set up the interval graph: ")



    if Wshares > Vshares

        x=(muffins//students)-((V-1)*alpha)
        y=(muffins//students)-((W-1)*(1-alpha))
        middleshares= Wshares-Vshares

        if alpha==1//3
            keylow=Int64(floor(Vshares/r))
            keyhigh= Int64(ceil(Vshares/r))
            other = W-keylow-1

            println("(",Vshares, " ", V, "-shares)(---0---)(", middleshares, " ", W, "-shares)(---0---)(", Vshares, " ", W, "-shares)")
            println(alpha, "       ", x, "    ", y, "       ", 1-y, "    ", 1-x, "       ", 1-alpha)

            check1=(keylow-1)*(1-alpha)+other*(y)
            check2=(keylow-1)*(1-alpha)+other*(1-y)
            check3=(keylow-1)*(1-x)+other*(1-y)
            println("Each student must have ", keylow, " largeshares. Verifying this: ")
            if check1>=muffins//students||check2<=muffins//students
                println("If a student has ", keylow, " largeshares and ", W-keylow, " smallshares they can atmost have ", muffins//students, " in total, which works!")
                if check3<=muffins//students
                    println("We can also check this in this way - if a student has ",  W-keylow, " ", 1-x, " size shares, they have <= ", muffins//students)
                    println("Therefore, ", alpha, " works as the upper bound with ", muffins, " muffins and ", students, " students")
                else
                    println("Alpha does not work, ", check3)
                end
            else
                println("Alpha does not work")
            end

        elseif alpha>=x||x>=y
            print("BOUND ERROR - the graph is incorrect")
            println("")
        else
            keylow=Int64(floor(Vshares/r))
            keyhigh= Int64(ceil(Vshares/r))
            other = W-keylow

            println("(",Vshares, " ", V, "-shares)(---0---)(", middleshares, " ", W, "-shares)(---0---)(", Vshares, " ", W, "-shares)")
            println(alpha, "        ", x, "  ", y, "       ", 1-y, " ", 1-x, "        ", 1-alpha)
            println("")
            println("We will call shares between ", 1-x, " and ", 1-alpha, " large-shares. Similarly those between ", y, " and ", 1-y, " are small shares")
            println("The bounds are derived in the graph from this logic - ")
            println("Since there are no shares between ", x, " and ", y, ", there must be no shares b/w their buddies, ", 1-y, " and ", 1-x)
            println("Also, since there are ", Vshares, " ", V, "-shares b/w ", alpha, " and ", x, " there must be the same number of ", W, "-shares with their buddies, leaving ", middleshares, " shares in between ", y, " and ", 1-y)
            println("The half method won't work here, since 1/2 of ", students, "//", students, " = ", students/2, "//", students, ", 1/2 is inside the interval with more shares, causing the half method to be innacurate")
            println("")

            if keyhigh*r>Vshares
                newdown=1-muffins//students+(W-1)
                answer= (keylow+other*newdown-muffins//students)//(keylow+other*(W-1))
                println("If each student has at least ", keyhigh, " ", "large-shares, then is a contradiction since we only have ", Vshares, " ", W, "-shares, not ", keyhigh*r)
                println("Each student must have ", keylow, " large shares. Verifying this: ")
                println("")


                check1=keylow*(1-alpha)+(W-keylow)*(y)
                check2=keylow*(1-alpha)+(W-keylow)*(1-y)
                check3=(keylow)*(1-x)+(W-keylow)*(1-y)
                if check1==muffins//students||check2==muffins//students
                    println("If a student has ", keylow, " largeshares and ", W-keylow, " smallshares they can atmost have ", muffins//students, " in total, which works!")
                    if check3<=muffins//students
                        println("We can also check this in this way - if a student has ", keylow, " ", 1-y, " largeshares and ", W-keylow, " ", 1-x, " smallshares, they have <= ", muffins//students)
                        println("Therefore, ", alpha, " works as the upper bound with ", muffins, " muffins and ", students, " students")
                    else
                        println("Alpha does not work, ", check3)
                    end
                else
                    println("Alpha does not work")
                end
            else
                println("Error")
            end
        end



    elseif Vshares>Wshares
        y=1-(muffins//students-((V-1)*alpha))
        x=1-(muffins//students-((W-1)*(1-alpha)))
        if alpha>=x||x>=y
            println("BOUND ERROR")
        else
            middleshares=Vshares-Wshares
            println("(",Wshares, " ", V, "-shares)(---0---)(", middleshares, " ", V, "-shares)(---0---)(", Wshares, " ", W, "-shares)")
            println(alpha, "      ", x, " ", y, "           ", 1-y, "  ", 1-x, "        ", 1-alpha)
            println("")
            println("Since 1/2 of ", students, "//", students, " = ", students/2, "//", students, ", 1/2 is inside the interval with more shares, causing the half method to be innacurate")
            println("The bounds are derived in the graph from this logic - since there are no shares between ", x, " and ", y, ", there must be no shares b/w their buddies")
            println("Also, since there are ", Wshares, " ", W, "-shares b/w ", 1-x, " and ", 1-alpha, " there must be an equal number of ", V, "-shares with their buddies")


            keylow=Int64(floor((Vshares-Wshares)/q))
            keyhigh=Int64(ceil((Vshares-Wshares)/q))
            other=V-keylow
            answer=(other*(1-muffins//students+(W-1))+(keylow-1)*(muffins//students))//(other+keylow*(V-1))
            println("If each student has at least ", keyhigh, " ", V, "-shares, then is a contradiction since we only have ", middleshares, " ", V, "-shares, not ", keyhigh*q)
            println("Each student has ", keylow, " large shares. Verifying this: ")
            println("")

            check1=keylow*(1-y)+(V-keylow)*x
            check2=keylow*(1-y)+(V-keylow)*alpha
            check3=keylow*(y)+(V-keylow)*x
            if check1==muffins//students||check2==muffins//students
                println("If a student has ", keylow, " largeshares and ", V-keylow, " smallshares they can atmost have ", muffins//students, " in total, which works!")
                if check3<=muffins//students
                    println("We can also check this in this way - if a student has ", keylow, " ", y, " largeshares and ", V-keylow, " ", x, " smallshares, they have <= ", muffins//students)
                    println("Therefore, ", alpha, " works as the upper bound with ", muffins, " muffins and ", students, " students")
                else
                    println("Alpha does not work because lowerbounds are greater than, ", muffins//students)
                end
            else
                println("Alpha does not work, verification failed")
                println("check 1 - ", check1, " check 2 - ", check2, " check 3  - ", check3)
            end
        end
    end
end
function int(muffins,students)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    q = Int64(2*muffins - W*students)
    r = Int64(V*students - 2*muffins)
    Wshares=W*r
    Vshares=V*q

    if Wshares>Vshares
        newdown1=1-muffins//students+(W-1)
        newdown2=1-muffins//students
        key=Int64(floor(Vshares/r))
        other=W-key
        answer1= (key+other*newdown1-muffins//students)//(key+other*(W-1))
        answer2=(muffins//students-(V-other)*(newdown2)-(other-1)*(1-newdown1))//((V-other)*(V-1)-(other-1)*(W-1))
        if answer1<=1//3
            return 1//3
        else
            return min(answer1, answer2)
        end

    else
        key=Int64(floor((Vshares-Wshares)/q))
        other=V-key
        answer=(other*(1-muffins//students+(W-1))+(key-1)*(muffins//students))//(other+key*(V-1))
        if answer<=1//3
            return 1//3
        else
            return answer
        end
    end


end

function fc(m,s)
	min1=m//(s*(Int)(ceil(2*m/s)))
	min2=1-m//(s*(Int)(floor(2m/s)))
	min3=min(min1,min2)

	if(m<s) return "m should be greater than or equal to s"
	elseif(m%s==0) return 1
    else return max(1//3,min3) 
    end
end

function vhalf(muffins, students,check)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//(students*(W-1)))
    upperproof=(muffins//(students*(V+1)))
    
    x = Int64((2*muffins - (W*students))/(V-W))
    y = Int64((2*muffins - (V*students))/(W-V))

    Wshares = W*y
	Vshares = V*x
	state =false
    if Wshares > muffins
        greaterhalf=Wshares
		key = W
		state=true
    elseif Vshares>muffins
        greaterhalf=Vshares
        key = V
    end
    
    halfsum=muffins//students-1//2

    firstbound=halfsum//(key-1)
    upperbound=max(firstbound, 1-firstbound)
    lowerbound=min(firstbound, 1-firstbound)

    if(lowerbound<=1//3&&V==3)
        println("This is a special case. The solution you get from the normal procedure is smaller than or equal to 1/3. Thus alpha will be 1/3 in this case ")
        println("( ", Vshares, " " , V, "-shares )( ", Wshares, " ", W, "-shares )")
        println("1/3          1/2          2/3")

    end

    if(lowerbound>1//3)
    println("If there is a student with less <= ", W-1," shares, one of the share's buddy is <= ", lowerproof, ", and if a student has >= ", V+1, " shares, one of the share is <= ", upperproof, " which are both smaller than ", fc(muffins,students))
    println("Thus, the student has less than ", V, " pieces or more than ", W, " pieces.")
    println("We can set up two equations: The total number of pieces is ", V, "{S_",V,"}+", W, "{S_",W,"}"," = ", 2*muffins, " and the total number of students is ","{S_",W,"}"," + ","{S_",V,"}", " = ", students)
    
    println("Once we solve, we get that ", x, " students get ", V, " pieces and ", y, " students get ", W, " pieces")
    println("(--------)-----(----------)")
    println(" ", V, "-shares", "  1/2   ", W, "-shares")
	
    if state
    println("We have ", greaterhalf," ", key, "-shares. Since we have ", muffins, " muffins, we cannot have all of ", greaterhalf," ", key,"-shares to be greater than 1/2")
    println("So some ", key, "-shares will be less than or equal to 1/2")
    elseif !state
    println("We have ", greaterhalf," ", key, "-shares. Since we have ", muffins, " muffins, we cannot have all of ", greaterhalf," ", key,"-shares to be less than 1/2")
    println("So some ", key, "-shares will be greater than or equal to 1/2")
    end

    
    println("The sum of all ", key, "-shares is ", muffins//students, ". If one share is 1/2, then the sum of the remaining shares is ", halfsum)
    
	println("There are ", key-1, " remaining shares. We divide ", halfsum, " by ", key-1, " to get the upper bound, which is ", upperbound)
	println("The buddy of ", upperbound, " is ", lowerbound)
	println("( ", Vshares, " " , V, "-shares )[0]( ", Wshares, " ", W, "-shares )")
	if state
    println(lowerbound, "    ",muffins//students-lowerbound*(V-1) ,"    ",1//2 ,"     ",upperbound )

    if (muffins//students-lowerbound*(V-1))>1//2
        println("In this case, the interavals overlap. So it requires two digrams")
        println("( ", Vshares, " " , V, "-shares )(   0   )")
        println(lowerbound, "    ",muffins//students-lowerbound*(V-1),"      ", upperbound)
        println("(    0    )","( ", Wshares, " " , W, "-shares )")
        println(lowerbound, "    1//2      ", upperbound)

    end

    elseif !state 
	println(lowerbound,"      ", 1//2,"  ",(muffins//students)-upperbound*(W-1) ,"        ", upperbound )
    end
    
    println("This should match with the following verified graph solution")
    firstbound= muffins//students-check*(V-1)
    secondbound=muffins//students-(1-check)*(W-1)
    println("( ", Vshares, " " , V, "-shares )[0]( ", Wshares, " ", W, "-shares )")
    println(check, "    ",firstbound ,"    ",secondbound ,"     ",1-check )
end
end


function half(muffins,students)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    lowerproof= 1-(muffins//(students*(W-1)))
    upperproof=(muffins//(students*(V+1)))
    
    x = Int64((2*muffins - (W*students))/(V-W))
    y = Int64((2*muffins - (V*students))/(W-V))

    Wshares = W*y
	Vshares = V*x
	state =false
    if Wshares > muffins
        greaterhalf=Wshares
		key = W
		state=true
    elseif Vshares>muffins
        greaterhalf=Vshares
        key = V
    end
    
    halfsum=muffins//students-1//2

    firstbound=halfsum//(key-1)
    upperbound=max(firstbound, 1-firstbound)
    lowerbound=min(firstbound, 1-firstbound)
    solution=lowerbound

    if(lowerbound<=1//3&&V==3)
        solution=1//3

    end
    println(solution)
end


function findproc(muffins,students,alpha)
    V = Int64(ceil((2 * muffins)/students))
    W = V-1
    d= denominator(alpha)
    total= (muffins//students)*d
    n=V
    for i =0:n
        for j=i:n
            
            if i*5+(j-i)*6+(n-j)*7==total
                println( i, j - i, n - j) 
            end
        end
    end 
    n=W
    for i =0:n
        for j=i:n
            
            if i*5+(j-i)*6+(n-j)*7==total
                println( i, j - i, n - j) 
            end
        end
    end 

end