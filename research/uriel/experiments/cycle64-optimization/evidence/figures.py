"""Render the exact tabulations as vector figures. All numeric inputs are published."""
import json
from fractions import Fraction as F
from pathlib import Path

def render():
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    root=Path(__file__).resolve().parent
    out=root.parent/"figures"
    out.mkdir(exist_ok=True)
    plt.rcParams.update({"font.size":10,"axes.spines.top":False,"axes.spines.right":False,
                         "pdf.fonttype":42,"axes.labelcolor":"#20333c","text.color":"#20333c"})
    def save(fig,name):
        fig.savefig(out/name,bbox_inches="tight",metadata={"CreationDate":None,"ModDate":None})
        plt.close(fig)
    rows=json.loads((root/"geometry/results.json").read_text())["rows"][:8]
    x=[float(F(r["cap"])) for r in rows]
    fig,ax=plt.subplots(figsize=(6.65,3.25))
    for k,label,color,marker in [("both","Both directions","#146567","o"),
                                  ("oriented_only","One direction only","#95513a","s")]:
        ax.plot(x,[100*float(F(r[k]["optimum"])) for r in rows],marker=marker,color=color,
                label=label,linewidth=1.4,markersize=5)
    ax.set(xlabel="Maximum rate per residue, in units of the source density",
           ylabel="Upper bound (%)",ylim=(-2,79),xticks=[1,1.5,2,2.4,3,4])
    ax.grid(axis="y",color="#d9dfdf",linewidth=.65)
    ax.legend(frameon=False,loc="upper left")
    save(fig,"geometry.pdf")
    rates=json.loads((root/"rates/results.json").read_text())
    cells=rates["adverse_label"]["rates_in_physical_order"]
    z=F(rates["arbitrary_individual_rates"]["lower"])
    ordered=sorted((float(p-z*q),t) for t,p,q in cells)
    fig,ax=plt.subplots(figsize=(6.65,3.1))
    for i,(margin,t) in enumerate(ordered):
        tone="#a14d30" if t==1 else "#2e4164" if t==2 else "#1c696b"
        ax.vlines(i,0,margin,color=tone,linewidth=1.1)
        ax.scatter(i,margin,s=15,color=tone,zorder=2)
        if t in (1,2):
            ax.annotate("residue "+str(t),(i,margin),xytext=(5,-3),textcoords="offset points",
                        fontsize=8,color=tone,ha="left")
    ax.axhline(0,color="#899999",linewidth=.8)
    ax.set(xlabel="Occupied residues, ordered by surplus per unit of rate",
           ylabel="Surplus per unit of rate",xticks=[])
    save(fig,"rates.pdf")
    data=json.loads((root/"lower/results.json").read_text())["sparse_search"]
    fig,ax=plt.subplots(figsize=(6.65,2.9))
    for j,row in enumerate(data):
        target=100*float(F(row["target"]))
        ax.plot([0,row["single_pass"]],[j,j],color="#246466",linewidth=5,solid_capstyle="butt")
        ax.plot([row["single_pass"],row["either_pass"]],[j,j],color="#c18148",linewidth=5,solid_capstyle="butt")
        ax.scatter(row["either_pass"],j,color="#a86032",s=13)
        ax.annotate(f"{row['charts']-row['either_pass']:,} open",(row["either_pass"],j),
                    xytext=(5,3),textcoords="offset points",fontsize=8)
    ax.set(yticks=range(len(data)),yticklabels=[f"{100*float(F(r['target'])):g}%" for r in data],
           xlim=(14900,16950),xticks=[15000,15500,16000,16384],xlabel="Normalized charts certified (16,384 total)",
           ylabel="Requested floor",ylim=(-.5,len(data)-.45))
    ax.axvline(16384,lw=.7,color="#aab6b4",zorder=0);ax.invert_yaxis()
    save(fig,"coverage.pdf")

if __name__=="__main__":
    render()
