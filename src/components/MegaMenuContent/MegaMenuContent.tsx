// Generated with util/create-component.js
import React from "react";
import { MegaMenuContentProps } from "./MegaMenuContent.types";
import Grid from "@mui/material/Grid";
import Typography from "@mui/material/Typography";
import Box from "@mui/material/Box";
import Linked from "components/Linked/Linked";
import Card from "@mui/material/Card";
import CardActionArea from "@mui/material/CardActionArea";
import CardContent from "@mui/material/CardContent";
const MegaMenuContent: React.FC<MegaMenuContentProps> = ({ content }) => {
  return (
    <>
      <Grid
        container
        sx={{
          maxWidth: "800px",
          px: 2,
          py: 1,
        }}
      >
        {content?.sections.map((section, index) => {
          return (
            <Grid item xs={12} key={index}>
              <Grid container>
                <Grid item xs={12}>
                  <Typography
                    variant="h6"
                    gutterBottom
                    sx={{ fontWeight: "bold" }}
                  >
                    {section.title}
                  </Typography>
                </Grid>
                {section.options.map((section, index) => {
                  return (
                    <Grid item xs={12} sm={6} key={index}>
                      <Card component={Linked} to={section.pathname}>
                        <CardActionArea>
                          <CardContent>
                            <Typography
                              component={"h3"}
                              variant={"h6"}
                              sx={{ fontWeight: "bold" }}
                            >
                              {section.title}
                            </Typography>
                            {section.description && (
                              <Typography component={"div"} variant={"body2"}>
                                {section.description}
                              </Typography>
                            )}
                          </CardContent>
                        </CardActionArea>
                      </Card>
                    </Grid>
                  );
                })}
              </Grid>
            </Grid>
          );
        })}
      </Grid>
    </>
  );
};
export default MegaMenuContent;
