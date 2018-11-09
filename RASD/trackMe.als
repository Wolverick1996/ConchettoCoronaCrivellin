open util/integer
open util/boolean

sig Position{
coordX: one Int,
coordY: one Int, 
}
{ coordX >= -3 and coordX =< 3 and coordY >= -6 and coordY =< 6 }

sig Track{
startPoint: one Position,
endPoint: one Position,
trackLenght: one Int,
stages: set Position
}
{((startPoint.coordX = endPoint.coordX and startPoint.coordY = endPoint.coordY) implies #stages > 0) and
(trackLenght > 0 and trackLenght =< 50)}

abstract sig Data{}

sig BPM extends Data{
value: one Int
}

sig BloodPressure extends Data{
value: one Int
}

sig Steps extends Data{}

sig Temperature extends Data{}

sig Glucose extends Data{
value: one Int
}

sig GenericUser{
bpmUser: one BPM,
bloodPressureUser: one BloodPressure,
stepsUser: one Steps,
temperatureUser: one Temperature,
glucoseUser: one Glucose,
locationUser: one Position,
givesAnonymizedData: one Bool,
surveysAllowed: set Survey,
notifications: set Notifications
}

abstract sig Survey{
surveyID: one Int,
involvedThirdParty: one ThirdParty,
researchResult: set GenericUser
}
{#researchResult > 0}

sig AnonymizedDataSurvey extends Survey{}
{#researchResult > 3}

sig SpecificIndividualsDataSurvey extends Survey{}
{#researchResult =< 3}

abstract sig Notification{}

sig SignedOutFromSurvey extends Notification{
userInvolved: one User
}

sig SignedInASurvey extends Notification{
surveyInvolved: one Survey
}

sig Warning extends Notification{}

sig CallAmbulanceWarning extends Warning{
userWhoNeedsHelp: one User
}

sig ThirdParty{
surveysCarriedOut: set Survey,
notifications: set Notification
}

sig EmergencyDispatcher{
warnings: set Warning
}

--TODO TRACK4RUN
-------------------------------------------------------------------

fact SurveysIdAreUnique{
no disj ss1, ss2: SpecificIndividualsDataSurvey|no disj as1, as2: AnonymizedDataSurvey|
	(ss1.surveyID = ss2.surveyID and   as1.surveyID = as2.surveyID and  ss1.surveyID = as1.surveyID and
	 ss1.surveyID = as2.surveyID and  ss2.surveyID = as2.surveyID and  as1.surveyID = ss2.surveyID)
}

fact NotificationSentToUserCausedBySurvey{
all user: GenericUser| all specificSurvey:  SpecificIndividualsDataSurvey|
 user in specificSurvey and  
}

